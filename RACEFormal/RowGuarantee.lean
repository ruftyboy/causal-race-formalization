import RACEFormal.CausalAssembly

open scoped BigOperators

namespace RACEFormal

/--
The deterministic causal-row bound in the notation of the research note.
Writing the exact prefix mass as `s = ∑ a_j` and the average prefix mass as
`α = s / m`, the entrywise bias/variance theorem becomes

`output_error ≤ D * min 1 ((u + B) / α)`.
-/
theorem bias_variance_to_output_bound_average_mass
    {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hm : 0 < m)
    (a mu b : Fin m → ℝ) (V : Fin m → E) (D u B : ℝ)
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (hA : 0 < ∑ j, a j) (hB : 0 < ∑ j, b j)
    (hD : 0 ≤ D) (hu : 0 ≤ u) (hBias : 0 ≤ B)
    (hdiam : ∀ j k, ‖V j - V k‖ ≤ D)
    (hvariance : ∀ j, |b j - mu j| ≤ u)
    (hbias : ∀ j, |mu j - a j| ≤ B) :
    ‖∑ j, (b j / (∑ i, b i) - a j / (∑ i, a i)) • V j‖
      ≤ D * min 1 ((u + B) / ((∑ i, a i) / (m : ℝ))) := by
  have h := bias_variance_to_output_bound
    a mu b V D u B ha hb hA hB hD hu hBias hdiam hvariance hbias
  have hmR : (m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hm)
  have hAR : (∑ i, a i) ≠ 0 := ne_of_gt hA
  have hratio :
      ((m : ℝ) * (u + B)) / (∑ i, a i) =
        (u + B) / ((∑ i, a i) / (m : ℝ)) := by
    field_simp [hmR, hAR]
  rw [← hratio]
  exact h

end RACEFormal
