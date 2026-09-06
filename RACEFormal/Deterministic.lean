import RACEFormal.Normalization
import RACEFormal.Diameter

open scoped BigOperators

namespace RACEFormal

/-- The normalized attention-output error is controlled by score L1 error times the value diameter. -/
theorem normalized_output_eta_bound
    {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : Fin m → ℝ) (V : Fin m → E) (D : ℝ)
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (hA : 0 < ∑ j, a j) (hB : 0 < ∑ j, b j)
    (hD : 0 ≤ D) (hdiam : ∀ j k, ‖V j - V k‖ ≤ D) :
    ‖∑ j, (b j / (∑ i, b i) - a j / (∑ i, a i)) • V j‖
      ≤ D * ((∑ j, |a j - b j|) / (∑ i, a i)) := by
  let A : ℝ := ∑ j, a j
  let B : ℝ := ∑ j, b j
  let η : ℝ := ∑ j, |a j - b j|
  let d : Fin m → ℝ := fun j => b j / B - a j / A
  have hApos : 0 < A := by simpa [A] using hA
  have hBpos : 0 < B := by simpa [B] using hB
  have hA0 : A ≠ 0 := ne_of_gt hApos
  have hB0 : B ≠ 0 := ne_of_gt hBpos

  have ha_sum_one : ∑ j, a j / A = 1 := by
    rw [← Finset.sum_div]
    simp [A, hA0]
  have hb_sum_one : ∑ j, b j / B = 1 := by
    rw [← Finset.sum_div]
    simp [B, hB0]
  have hd_sum : ∑ j, d j = 0 := by
    simp only [d]
    rw [Finset.sum_sub_distrib, hb_sum_one, ha_sum_one, sub_self]

  have hl1_forward :
      (∑ j, |a j / A - b j / B|) ≤ 2 * η / A := by
    simpa [A, B, η] using normalization_l1_bound a b ha hb hA hB
  have hl1_reverse :
      (∑ j, |d j|) ≤ 2 * η / A := by
    have heq : (∑ j, |d j|) = ∑ j, |a j / A - b j / B| := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [d]
      rw [abs_sub_comm]
    rw [heq]
    exact hl1_forward

  have hgeom := zero_sum_weighted_diameter_bound d V D hD hd_sum hdiam
  have hDhalf : 0 ≤ D / 2 := div_nonneg hD (by norm_num)
  have hscaled :
      (D / 2) * (∑ j, |d j|) ≤ (D / 2) * (2 * η / A) :=
    mul_le_mul_of_nonneg_left hl1_reverse hDhalf
  have hfinal : ‖∑ j, d j • V j‖ ≤ D * (η / A) := by
    calc
      ‖∑ j, d j • V j‖ ≤ (D / 2) * ∑ j, |d j| := hgeom
      _ ≤ (D / 2) * (2 * η / A) := hscaled
      _ = D * (η / A) := by ring

  simpa [A, B, η, d] using hfinal

/-- Independently of score error, two normalized nonnegative weighted averages stay within the
value diameter. -/
theorem normalized_output_diameter_cap
    {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : Fin m → ℝ) (V : Fin m → E) (D : ℝ)
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (hA : 0 < ∑ j, a j) (hB : 0 < ∑ j, b j)
    (hdiam : ∀ j k, ‖V j - V k‖ ≤ D) :
    ‖∑ j, (b j / (∑ i, b i) - a j / (∑ i, a i)) • V j‖ ≤ D := by
  let A : ℝ := ∑ j, a j
  let B : ℝ := ∑ j, b j
  let x : E := ∑ j, (a j / A) • V j
  let y : E := ∑ j, (b j / B) • V j
  have hApos : 0 < A := by simpa [A] using hA
  have hBpos : 0 < B := by simpa [B] using hB
  have hA0 : A ≠ 0 := ne_of_gt hApos
  have hB0 : B ≠ 0 := ne_of_gt hBpos
  have ha_sum_one : ∑ j, a j / A = 1 := by
    rw [← Finset.sum_div]
    simp [A, hA0]
  have hb_sum_one : ∑ j, b j / B = 1 := by
    rw [← Finset.sum_div]
    simp [B, hB0]
  have haw (j : Fin m) : 0 ≤ a j / A := div_nonneg (ha j) hApos.le
  have hbw (j : Fin m) : 0 ≤ b j / B := div_nonneg (hb j) hBpos.le

  let S : Set E := convexHull ℝ (Set.range V)
  have hSconv : Convex ℝ S := by
    simpa [S] using convex_convexHull ℝ (Set.range V)
  have hx : x ∈ S := by
    dsimp [x]
    apply hSconv.sum_mem
    · intro j hj
      exact haw j
    · simpa using ha_sum_one
    · intro j hj
      exact subset_convexHull ℝ (Set.range V) (Set.mem_range_self j)
  have hy : y ∈ S := by
    dsimp [y]
    apply hSconv.sum_mem
    · intro j hj
      exact hbw j
    · simpa using hb_sum_one
    · intro j hj
      exact subset_convexHull ℝ (Set.range V) (Set.mem_range_self j)

  have hxy : ‖y - x‖ ≤ D := by
    have hx' : x ∈ convexHull ℝ (Set.range V) := by simpa [S] using hx
    have hy' : y ∈ convexHull ℝ (Set.range V) := by simpa [S] using hy
    rcases convexHull_exists_dist_ge2 hy' hx' with ⟨vy, hvy, vx, hvx, hdist⟩
    rcases hvy with ⟨j, rfl⟩
    rcases hvx with ⟨k, rfl⟩
    calc
      ‖y - x‖ = dist y x := by rw [dist_eq_norm]
      _ ≤ dist (V j) (V k) := hdist
      _ = ‖V j - V k‖ := dist_eq_norm _ _
      _ ≤ D := hdiam j k

  have hout :
      (∑ j, (b j / B - a j / A) • V j) = y - x := by
    calc
      (∑ j, (b j / B - a j / A) • V j)
          = ∑ j, ((b j / B) • V j - (a j / A) • V j) := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [sub_smul]
      _ = (∑ j, (b j / B) • V j) - (∑ j, (a j / A) • V j) := by
            rw [Finset.sum_sub_distrib]
      _ = y - x := by rfl

  change ‖∑ j, (b j / B - a j / A) • V j‖ ≤ D
  rw [hout]
  exact hxy

/--
Full deterministic diameter-sensitive normalization stability bound used in the strengthened
causal RACE note.  This formalizes the `D * min(1, η/A)` statement.
-/
theorem diameter_sensitive_normalization_stability
    {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : Fin m → ℝ) (V : Fin m → E) (D : ℝ)
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (hA : 0 < ∑ j, a j) (hB : 0 < ∑ j, b j)
    (hD : 0 ≤ D) (hdiam : ∀ j k, ‖V j - V k‖ ≤ D) :
    ‖∑ j, (b j / (∑ i, b i) - a j / (∑ i, a i)) • V j‖
      ≤ D * min 1 ((∑ j, |a j - b j|) / (∑ i, a i)) := by
  let e : ℝ := (∑ j, |a j - b j|) / (∑ i, a i)
  have heta :
      ‖∑ j, (b j / (∑ i, b i) - a j / (∑ i, a i)) • V j‖ ≤ D * e := by
    simpa [e] using normalized_output_eta_bound a b V D ha hb hA hB hD hdiam
  have hcap :
      ‖∑ j, (b j / (∑ i, b i) - a j / (∑ i, a i)) • V j‖ ≤ D :=
    normalized_output_diameter_cap a b V D ha hb hA hB hdiam
  by_cases he : e ≤ 1
  · rw [min_eq_right he]
    exact heta
  · have h1e : 1 ≤ e := le_of_lt (lt_of_not_ge he)
    rw [min_eq_left h1e]
    simpa using hcap

end RACEFormal
