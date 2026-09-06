import RACEFormal.ActualRaceSampler

open scoped BigOperators

namespace RACEFormal

/-- Exponential weight of one binary RACE hash coordinate. -/
noncomputable def raceBitExpWeight (beta z : ℝ) (b : Bool) : ℝ :=
  Real.exp (raceCornerSign b * (beta * Real.tanh z))

/-- One-bit exponential partition function. -/
noncomputable def raceBitExpPartition (beta z : ℝ) : ℝ :=
  ∑ b : Bool, raceBitExpWeight beta z b

/-- One-bit softmax probability in the literal exponential-logit representation. -/
noncomputable def raceBitExpSoftmax (beta z : ℝ) (b : Bool) : ℝ :=
  raceBitExpWeight beta z b / raceBitExpPartition beta z

/-- Elementary logistic identity for the negative exponential branch. -/
theorem exp_neg_ratio_eq_logistic (a : ℝ) :
    Real.exp (-a) / (Real.exp (-a) + Real.exp a) =
      1 / (1 + Real.exp (2 * a)) := by
  have hfac : Real.exp a = Real.exp (-a) * Real.exp (2 * a) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hfac]
  rw [show Real.exp (-a) + Real.exp (-a) * Real.exp (2 * a) =
      Real.exp (-a) * (1 + Real.exp (2 * a)) by ring]
  have hplus : 1 + Real.exp (2 * a) ≠ 0 := by positivity
  field_simp [Real.exp_ne_zero, hplus]

/-- Elementary logistic identity for the positive exponential branch. -/
theorem exp_pos_ratio_eq_one_sub_logistic (a : ℝ) :
    Real.exp a / (Real.exp (-a) + Real.exp a) =
      1 - 1 / (1 + Real.exp (2 * a)) := by
  have hfac : Real.exp a = Real.exp (-a) * Real.exp (2 * a) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hfac]
  rw [show Real.exp (-a) + Real.exp (-a) * Real.exp (2 * a) =
      Real.exp (-a) * (1 + Real.exp (2 * a)) by ring]
  have hplus : 1 + Real.exp (2 * a) ≠ 0 := by positivity
  field_simp [Real.exp_ne_zero, hplus]
  ring

/-- The sign of `tanh z` agrees with the sign of `z`. -/
theorem tanh_nonneg_of_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ Real.tanh z := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg ((Real.sinh_nonneg_iff).2 hz) (Real.cosh_pos z).le

/-- The sign of `tanh z` agrees with the sign of `z`. -/
theorem tanh_nonpos_of_nonpos {z : ℝ} (hz : z ≤ 0) : Real.tanh z ≤ 0 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonpos_of_nonpos_of_nonneg ((Real.sinh_nonpos_iff).2 hz) (Real.cosh_pos z).le

/-- The literal binary exponential softmax is exactly the leakage-form bit distribution. -/
theorem raceBitExpSoftmax_eq_softBitProb (beta z : ℝ) (b : Bool) :
    raceBitExpSoftmax beta z b = softBitProb beta z b := by
  by_cases hz : 0 ≤ z
  · have ht : 0 ≤ Real.tanh z := tanh_nonneg_of_nonneg hz
    have habs : |Real.tanh z| = Real.tanh z := abs_of_nonneg ht
    cases b with
    | false =>
        simpa [raceBitExpSoftmax, raceBitExpPartition, raceBitExpWeight,
          raceCornerSign, Fintype.sum_bool, softBitProb, hardBit, hz,
          softLeak, habs, mul_assoc, add_comm] using
          exp_neg_ratio_eq_logistic (beta * Real.tanh z)
    | true =>
        simpa [raceBitExpSoftmax, raceBitExpPartition, raceBitExpWeight,
          raceCornerSign, Fintype.sum_bool, softBitProb, hardBit, hz,
          softLeak, habs, mul_assoc, add_comm] using
          exp_pos_ratio_eq_one_sub_logistic (beta * Real.tanh z)
  · have hz' : z ≤ 0 := le_of_not_ge hz
    have ht : Real.tanh z ≤ 0 := tanh_nonpos_of_nonpos hz'
    have habs : |Real.tanh z| = -Real.tanh z := abs_of_nonpos ht
    cases b with
    | false =>
        simpa [raceBitExpSoftmax, raceBitExpPartition, raceBitExpWeight,
          raceCornerSign, Fintype.sum_bool, softBitProb, hardBit, hz,
          softLeak, habs, mul_assoc, add_comm] using
          exp_pos_ratio_eq_one_sub_logistic (-(beta * Real.tanh z))
    | true =>
        simpa [raceBitExpSoftmax, raceBitExpPartition, raceBitExpWeight,
          raceCornerSign, Fintype.sum_bool, softBitProb, hardBit, hz,
          softLeak, habs, mul_assoc, add_comm] using
          exp_neg_ratio_eq_logistic (-(beta * Real.tanh z))

/-- The explicit RACE corner exponential weight factors over hyperplanes. -/
theorem raceCornerWeight_eq_bitExpProduct {d Pbits : ℕ}
    (beta : ℝ) (planes : Fin Pbits → RaceHyperplane d)
    (x : RaceAmbient d) (v : RaceCorner Pbits) :
    raceCornerWeight beta planes x v =
      ∏ bit, raceBitExpWeight beta (raceProjection (planes bit) x) (v bit) := by
  unfold raceCornerWeight raceCornerLogit raceBitExpWeight
  rw [← Real.exp_sum]
  apply congrArg Real.exp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro bit _
  ring

/-- The full `2^Pbits` corner partition function factors into binary partitions. -/
theorem raceCornerPartition_eq_bitExpPartitions {d Pbits : ℕ}
    (beta : ℝ) (planes : Fin Pbits → RaceHyperplane d)
    (x : RaceAmbient d) :
    raceCornerPartition beta planes x =
      ∏ bit, raceBitExpPartition beta (raceProjection (planes bit) x) := by
  unfold raceCornerPartition
  simp_rw [raceCornerWeight_eq_bitExpProduct]
  simpa [raceBitExpPartition] using
    (product_corner_mass_factorization Pbits
      (fun bit b => raceBitExpWeight beta (raceProjection (planes bit) x) b))

/--
The literal `2^Pbits` softmax used by RACE is exactly the product-form corner
probability used in the finite-temperature proof.
-/
theorem raceCornerSoftmax_eq_productCornerFeature {d Pbits : ℕ}
    (beta : ℝ) (planes : Fin Pbits → RaceHyperplane d)
    (x : RaceAmbient d) (v : RaceCorner Pbits) :
    raceCornerSoftmax beta planes x v =
      raceProductCornerFeature beta planes x v := by
  unfold raceCornerSoftmax raceProductCornerFeature
  rw [raceCornerWeight_eq_bitExpProduct, raceCornerPartition_eq_bitExpPartitions]
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro bit _
  exact raceBitExpSoftmax_eq_softBitProb beta (raceProjection (planes bit) x) (v bit)

/--
Hence the inner product of the implementation's explicit corner softmaxes is
exactly the factorized soft RACE table kernel already used by the proof.
-/
theorem explicitCornerSoftmaxKernel_eq_raceSoftTableKernel {d Pbits : ℕ}
    (beta : ℝ) (planes : Fin Pbits → RaceHyperplane d)
    (q k : RaceAmbient d) :
    (∑ v : RaceCorner Pbits,
      raceCornerSoftmax beta planes q v * raceCornerSoftmax beta planes k v) =
      raceSoftTableKernel beta planes q k := by
  unfold raceSoftTableKernel
  simp_rw [raceCornerSoftmax_eq_productCornerFeature]

/-- Literal logit scale from the reference implementation: `tanh(proj) / sqrt(d)`. -/
noncomputable def raceImplementationBeta (d : ℕ) : ℝ :=
  1 / Real.sqrt d

/--
The generic `beta` corner logit specializes exactly to the implementation's
`(tanh(proj) / sqrt(d)) @ corner` expression.
-/
theorem raceCornerLogit_implementation_scale {d Pbits : ℕ}
    (planes : Fin Pbits → RaceHyperplane d)
    (x : RaceAmbient d) (v : RaceCorner Pbits) :
    raceCornerLogit (raceImplementationBeta d) planes x v =
      ∑ bit, (Real.tanh (raceProjection (planes bit) x) / Real.sqrt d) *
        raceCornerSign (v bit) := by
  unfold raceCornerLogit raceImplementationBeta
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro bit _
  ring

end RACEFormal
