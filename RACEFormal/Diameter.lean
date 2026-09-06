import Mathlib

open scoped BigOperators

namespace RACEFormal

/--
A zero-mass signed combination of points with diameter at most `D` has norm at most
`D/2` times the L1 mass of the coefficients.  This is the geometric half of the
RACE normalization-stability lemma.
-/
theorem zero_sum_weighted_diameter_bound
    {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : Fin m → ℝ) (V : Fin m → E) (D : ℝ)
    (hD : 0 ≤ D)
    (hsum : ∑ j, d j = 0)
    (hdiam : ∀ j k, ‖V j - V k‖ ≤ D) :
    ‖∑ j, d j • V j‖ ≤ (D / 2) * ∑ j, |d j| := by
  let r : Fin m → ℝ := fun j => (d j)⁺
  let n : Fin m → ℝ := fun j => (d j)⁻
  let M : ℝ := ∑ j, r j

  have hr_nonneg (j : Fin m) : 0 ≤ r j := by
    simp [r]
  have hn_nonneg (j : Fin m) : 0 ≤ n j := by
    simp [n]
  have hdecomp (j : Fin m) : r j - n j = d j := by
    simpa [r, n] using posPart_sub_negPart (d j)
  have habs (j : Fin m) : r j + n j = |d j| := by
    simpa [r, n] using posPart_add_negPart (d j)

  have hmass_eq : (∑ j, r j) = ∑ j, n j := by
    have : (∑ j, r j) - (∑ j, n j) = 0 := by
      rw [← Finset.sum_sub_distrib]
      simpa [hdecomp] using hsum
    linarith
  have hn_sum : (∑ j, n j) = M := by
    simpa [M] using hmass_eq.symm
  have hl1 : (∑ j, |d j|) = 2 * M := by
    calc
      (∑ j, |d j|) = ∑ j, (r j + n j) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact (habs j).symm
      _ = (∑ j, r j) + (∑ j, n j) := Finset.sum_add_distrib
      _ = M + M := by simp [M, hn_sum]
      _ = 2 * M := by ring

  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact Finset.sum_nonneg fun j hj => hr_nonneg j

  by_cases hM0 : M = 0
  · have hr_zero : ∀ j, r j = 0 := by
      have hz := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j (_ : j ∈ Finset.univ) => hr_nonneg j)).1 (by simpa [M] using hM0)
      intro j
      exact hz j (Finset.mem_univ j)
    have hn_zero : ∀ j, n j = 0 := by
      have hnSum0 : ∑ j, n j = 0 := by simpa [hn_sum, hM0]
      have hz := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j (_ : j ∈ Finset.univ) => hn_nonneg j)).1 hnSum0
      intro j
      exact hz j (Finset.mem_univ j)
    have hd_zero : ∀ j, d j = 0 := by
      intro j
      rw [← hdecomp j, hr_zero j, hn_zero j]
      simp
    simp [hd_zero]
  · have hMpos : 0 < M := lt_of_le_of_ne hM_nonneg (Ne.symm hM0)
    let x : E := ∑ j, (r j / M) • V j
    let y : E := ∑ j, (n j / M) • V j

    have hr_sum_one : ∑ j, r j / M = 1 := by
      rw [← Finset.sum_div]
      simp [M, hM0]
    have hn_sum_one : ∑ j, n j / M = 1 := by
      rw [← Finset.sum_div, hn_sum]
      simp [hM0]
    have hrw_nonneg (j : Fin m) : 0 ≤ r j / M := div_nonneg (hr_nonneg j) hM_nonneg
    have hnw_nonneg (j : Fin m) : 0 ≤ n j / M := div_nonneg (hn_nonneg j) hM_nonneg

    let S : Set E := convexHull ℝ (Set.range V)
    have hSconv : Convex ℝ S := by
      simpa [S] using convex_convexHull ℝ (Set.range V)
    have hx : x ∈ S := by
      dsimp [x]
      apply hSconv.sum_mem
      · intro j hj
        exact hrw_nonneg j
      · simpa using hr_sum_one
      · intro j hj
        exact subset_convexHull ℝ (Set.range V) (Set.mem_range_self j)
    have hy : y ∈ S := by
      dsimp [y]
      apply hSconv.sum_mem
      · intro j hj
        exact hnw_nonneg j
      · simpa using hn_sum_one
      · intro j hj
        exact subset_convexHull ℝ (Set.range V) (Set.mem_range_self j)

    have hxy : ‖x - y‖ ≤ D := by
      have hx' : x ∈ convexHull ℝ (Set.range V) := by simpa [S] using hx
      have hy' : y ∈ convexHull ℝ (Set.range V) := by simpa [S] using hy
      rcases convexHull_exists_dist_ge2 hx' hy' with ⟨vx, hvx, vy, hvy, hdist⟩
      rcases hvx with ⟨j, rfl⟩
      rcases hvy with ⟨k, rfl⟩
      calc
        ‖x - y‖ = dist x y := by rw [dist_eq_norm]
        _ ≤ dist (V j) (V k) := hdist
        _ = ‖V j - V k‖ := dist_eq_norm _ _
        _ ≤ D := hdiam j k

    have hout_eq : (∑ j, d j • V j) = M • (x - y) := by
      calc
        (∑ j, d j • V j) = ∑ j, ((r j - n j) • V j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hdecomp j]
        _ = (∑ j, r j • V j) - (∑ j, n j • V j) := by
          simp_rw [sub_smul]
          rw [Finset.sum_sub_distrib]
        _ = M • x - M • y := by
          congr 1
          · dsimp [x]
            rw [Finset.smul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            rw [smul_smul]
            field_simp [hM0]
          · dsimp [y]
            rw [Finset.smul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            rw [smul_smul]
            field_simp [hM0]
        _ = M • (x - y) := by rw [smul_sub]

    calc
      ‖∑ j, d j • V j‖ = ‖M • (x - y)‖ := by rw [hout_eq]
      _ = M * ‖x - y‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hMpos]
      _ ≤ M * D := mul_le_mul_of_nonneg_left hxy hM_nonneg
      _ = (D / 2) * ∑ j, |d j| := by rw [hl1]; ring

end RACEFormal
