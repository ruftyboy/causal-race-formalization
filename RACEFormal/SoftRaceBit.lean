import RACEFormal.SoftHard

open scoped BigOperators

namespace RACEFormal

/--
Canonical hard sign bit.  We choose the positive bit at the zero-margin tie;
under a nondegenerate Gaussian law the tie has probability zero.
-/
noncomputable def hardBit (z : ℝ) : Bool := decide (0 ≤ z)

/--
The one-bit soft RACE distribution, written in the equivalent leakage form:
the dominant hard bit has mass `1 - softLeak beta z` and the other bit has
mass `softLeak beta z`.
-/
noncomputable def softBitProb (beta z : ℝ) (b : Bool) : ℝ :=
  if b = hardBit z then 1 - softLeak beta z else softLeak beta z

/-- Every one-bit soft probability is nonnegative. -/
theorem softBitProb_nonneg (beta z : ℝ) (b : Bool) :
    0 ≤ softBitProb beta z b := by
  unfold softBitProb
  by_cases h : b = hardBit z
  · rw [if_pos h]
    exact sub_nonneg.mpr (softLeak_le_one beta z)
  · rw [if_neg h]
    exact softLeak_nonneg beta z

/-- Every one-bit soft probability is at most one. -/
theorem softBitProb_le_one (beta z : ℝ) (b : Bool) :
    softBitProb beta z b ≤ 1 := by
  unfold softBitProb
  by_cases h : b = hardBit z
  · rw [if_pos h]
    linarith [softLeak_nonneg beta z]
  · rw [if_neg h]
    exact softLeak_le_one beta z

/-- The two soft bit masses sum exactly to one. -/
theorem softBitProb_mass_one (beta z : ℝ) :
    (∑ b : Bool, softBitProb beta z b) = 1 := by
  rw [Fintype.sum_bool]
  cases h : hardBit z <;> simp [softBitProb, h] <;> ring

/-- One-bit soft agreement, i.e. the inner product of the two binary soft distributions. -/
noncomputable def softBitAgreement (beta x y : ℝ) : ℝ :=
  ∑ b : Bool, softBitProb beta x b * softBitProb beta y b

/-- Hard one-bit collision indicator. -/
noncomputable def hardBitAgreement (x y : ℝ) : ℝ :=
  if hardBit x = hardBit y then 1 else 0

/-- The one-bit soft agreement is nonnegative. -/
theorem softBitAgreement_nonneg (beta x y : ℝ) :
    0 ≤ softBitAgreement beta x y := by
  unfold softBitAgreement
  exact Finset.sum_nonneg fun b _ =>
    mul_nonneg (softBitProb_nonneg beta x b) (softBitProb_nonneg beta y b)

/-- The one-bit soft agreement is at most one. -/
theorem softBitAgreement_le_one (beta x y : ℝ) :
    softBitAgreement beta x y ≤ 1 := by
  calc
    softBitAgreement beta x y
        = ∑ b : Bool, softBitProb beta x b * softBitProb beta y b := rfl
    _ ≤ ∑ b : Bool, softBitProb beta x b := by
      apply Finset.sum_le_sum
      intro b _hb
      have h := mul_le_mul_of_nonneg_left
        (softBitProb_le_one beta y b) (softBitProb_nonneg beta x b)
      simpa using h
    _ = 1 := softBitProb_mass_one beta x

/-- The hard collision indicator lies in `[0,1]`. -/
theorem hardBitAgreement_mem_Icc (x y : ℝ) :
    hardBitAgreement x y ∈ Set.Icc (0 : ℝ) 1 := by
  unfold hardBitAgreement
  by_cases h : hardBit x = hardBit y <;> simp [h]

/--
Pointwise soft-to-hard one-bit error.  It is controlled by the sum of the two
logistic leakage masses, with no independence assumption between the margins.
-/
theorem softBitAgreement_error_le_leakage (beta x y : ℝ) :
    |softBitAgreement beta x y - hardBitAgreement x y| ≤
      softLeak beta x + softLeak beta y := by
  have hx0 := softLeak_nonneg beta x
  have hx1 := softLeak_le_one beta x
  have hy0 := softLeak_nonneg beta y
  have hy1 := softLeak_le_one beta y
  cases hx : hardBit x <;> cases hy : hardBit y
  · simpa [softBitAgreement, hardBitAgreement, softBitProb, hx, hy,
      Fintype.sum_bool, add_comm] using
        same_sign_soft_agreement_error
          (softLeak beta x) (softLeak beta y) hx0 hx1 hy0 hy1
  · simpa [softBitAgreement, hardBitAgreement, softBitProb, hx, hy,
      Fintype.sum_bool, add_comm] using
        opposite_sign_soft_agreement_error
          (softLeak beta x) (softLeak beta y) hx0 hx1 hy0 hy1
  · simpa [softBitAgreement, hardBitAgreement, softBitProb, hx, hy,
      Fintype.sum_bool, add_comm] using
        opposite_sign_soft_agreement_error
          (softLeak beta x) (softLeak beta y) hx0 hx1 hy0 hy1
  · simpa [softBitAgreement, hardBitAgreement, softBitProb, hx, hy,
      Fintype.sum_bool, add_comm] using
        same_sign_soft_agreement_error
          (softLeak beta x) (softLeak beta y) hx0 hx1 hy0 hy1

end RACEFormal
