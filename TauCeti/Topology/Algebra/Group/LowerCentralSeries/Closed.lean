/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.LowerCentralSeries

/-!
# The closed lower central series of a topological group

The **closed lower central series** of a topological group `G` is the sequence of closed normal
subgroups

```text
γ₀ = G,   γ_{n+1} = closure [γ_n, G],
```

the case `p = 0` of the lower `p`-series `TauCeti.pLowerCentralSeries`: at `p = 0` the power term
`λ_nᵖ` of the step `closure (λ_nᵖ ⬝ [λ_n, G])` is trivial. It is defined as that case, so the
closedness, normality, antitonicity, degree-raising law `⁅γ_j, γ_k⁆ ≤ γ_{j+k+1}` and
functoriality proved for the lower `p`-series apply to it, and are recorded here in the notation of
the closed series. The degree-raising law is what makes the commutator induce a graded bracket on
the successive quotients `γ_n ⧸ γ_{n+1}`, which are `TauCeti.gradedPiece 0 G n`.

Each `γ_n` is the topological closure of the term `Subgroup.lowerCentralSeries ⊤ n` of the lower
central series of the underlying abstract group, because the commutator map is continuous. It is
topologically characteristic, and it is contained in every lower `p`-series term `λ_n`. In a
pro-`p` group the closed lower central series therefore has trivial intersection
(`TauCeti.IsProP.iInf_closedLowerCentralSeries_eq_bot`).

The terms `γ_n` are not open in general, unlike the `λ_n` of a topologically finitely generated
pro-`p` group: for the free pro-`p` group of rank two, `G ⧸ γ_1` is `ℤ_p ^ 2`.

## Main definitions

* `TauCeti.closedLowerCentralSeries`: the closed lower central series `γ_n`.

## Main results

* `TauCeti.closedLowerCentralSeries_succ`: `γ_{n+1} = closure ⁅γ_n, G⁆`.
* `TauCeti.commutator_closedLowerCentralSeries_le`: the degree-raising law
  `⁅γ_j, γ_k⁆ ≤ γ_{j+k+1}`.
* `MonoidHom.map_closedLowerCentralSeries_le`,
  `MonoidHom.map_closedLowerCentralSeries_eq_of_surjective`,
  `ContinuousMulEquiv.map_closedLowerCentralSeries_eq`: functoriality of the series.
* `TauCeti.isTopCharacteristic_closedLowerCentralSeries`: every term is topologically
  characteristic.
* `TauCeti.closedLowerCentralSeries_eq_topologicalClosure`: `γ_n` is the closure of the `n`-th term
  of the abstract lower central series.
* `TauCeti.closedLowerCentralSeries_le_pLowerCentralSeries`: `γ_n ≤ λ_n` for every `p`.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.8.
* J. D. Dixon, M. P. F. du Sautoy, A. Mann and D. Segal, *Analytic pro-`p` groups*, Section 1.2.
-/

public section

namespace TauCeti

open Subgroup

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The **closed lower central series** of a topological group, 0-based to match Mathlib's
`Subgroup.lowerCentralSeries`: `γ₀ = G` and `γ_{n+1} = closure ⁅γ_n, G⁆`
(`TauCeti.closedLowerCentralSeries_succ`). It is the case `p = 0` of the lower `p`-series
(`TauCeti.closedLowerCentralSeries_def`), and each term is the topological closure of the
corresponding term of the lower central series of the underlying group
(`TauCeti.closedLowerCentralSeries_eq_topologicalClosure`). -/
def closedLowerCentralSeries (n : ℕ) : Subgroup G :=
  pLowerCentralSeries 0 G n

/-- The closed lower central series is the lower `p`-series at `p = 0`. -/
theorem closedLowerCentralSeries_def (n : ℕ) :
    closedLowerCentralSeries G n = pLowerCentralSeries 0 G n := by
  rw [closedLowerCentralSeries]

/-- The zeroth term of the closed lower central series is the whole group. -/
@[simp]
theorem closedLowerCentralSeries_zero : closedLowerCentralSeries G 0 = ⊤ := by
  rw [closedLowerCentralSeries_def, pLowerCentralSeries_zero]

/-- The recursion of the closed lower central series: `γ_{n+1} = closure ⁅γ_n, G⁆`. -/
@[simp]
theorem closedLowerCentralSeries_succ (n : ℕ) :
    closedLowerCentralSeries G (n + 1) =
      ⁅closedLowerCentralSeries G n, (⊤ : Subgroup G)⁆.topologicalClosure := by
  rw [closedLowerCentralSeries_def, closedLowerCentralSeries_def, pLowerCentralSeries_succ]
  refine le_antisymm ((pLowerCentralStep_le_iff (isClosed_topologicalClosure _)).mpr
    ⟨fun x _ ↦ ?_, le_topologicalClosure _⟩)
    (topologicalClosure_minimal _ (commutator_le_pLowerCentralStep _)
      (isClosed_pLowerCentralStep _))
  rw [pow_zero]
  exact one_mem _

/-- The first term of the closed lower central series is the closure of the commutator subgroup,
the subgroup by which Mathlib's `TopologicalAbelianization` is the quotient. -/
theorem closedLowerCentralSeries_one :
    closedLowerCentralSeries G 1 = (commutator G).topologicalClosure := by
  rw [closedLowerCentralSeries_succ, closedLowerCentralSeries_zero, commutator_def]

variable {G}

/-- Every term of the closed lower central series is a normal subgroup. -/
instance closedLowerCentralSeries_normal (n : ℕ) : (closedLowerCentralSeries G n).Normal := by
  rw [closedLowerCentralSeries_def]
  infer_instance

/-- Every term of the closed lower central series is closed. -/
theorem isClosed_closedLowerCentralSeries (n : ℕ) :
    IsClosed (closedLowerCentralSeries G n : Set G) := by
  rw [closedLowerCentralSeries_def]
  exact isClosed_pLowerCentralSeries n

/-- The closed lower central series is antitone. -/
theorem closedLowerCentralSeries_antitone : Antitone (closedLowerCentralSeries G) := by
  intro m n h
  simp only [closedLowerCentralSeries_def]
  exact pLowerCentralSeries_antitone h

/-- **The degree-raising law.** Commutators of `γ_j` with `γ_k` lie in `γ_{j+k+1}`. -/
theorem commutator_closedLowerCentralSeries_le (j k : ℕ) :
    ⁅closedLowerCentralSeries G j, closedLowerCentralSeries G k⁆ ≤
      closedLowerCentralSeries G (j + k + 1) := by
  simp only [closedLowerCentralSeries_def]
  exact commutator_pLowerCentralSeries_le j k

/-- **Comparison with the abstract lower central series.** Every term of the closed lower central
series is the topological closure of the corresponding term of the lower central series of the
underlying group. -/
theorem closedLowerCentralSeries_eq_topologicalClosure (n : ℕ) :
    closedLowerCentralSeries G n = ((⊤ : Subgroup G).lowerCentralSeries n).topologicalClosure := by
  rw [closedLowerCentralSeries_def, pLowerCentralSeries_eq_topologicalClosure,
    pLowerCentralSeries_zero_left]

/-- **Comparison with the lower `p`-series.** For every `p`, each term of the closed lower central
series is contained in the corresponding term of the lower `p`-series. -/
theorem closedLowerCentralSeries_le_pLowerCentralSeries (p n : ℕ) :
    closedLowerCentralSeries G n ≤ pLowerCentralSeries p G n := by
  rw [closedLowerCentralSeries_eq_topologicalClosure, pLowerCentralSeries_eq_topologicalClosure]
  exact topologicalClosure_mono (lowerCentralSeries_le_pLowerCentralSeries p _ n)

/-! ### Functoriality -/

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- A continuous homomorphism carries `γ_n` into `γ_n`. -/
theorem _root_.MonoidHom.map_closedLowerCentralSeries_le (f : G →* H) (hf : Continuous f)
    (n : ℕ) : (closedLowerCentralSeries G n).map f ≤ closedLowerCentralSeries H n := by
  simp only [closedLowerCentralSeries_def]
  exact f.map_pLowerCentralSeries_le hf n

/-- A continuous closed surjection (for instance a continuous surjection from a compact group onto
a Hausdorff group, by `Continuous.isClosedMap`) carries `γ_n` onto `γ_n`. -/
theorem _root_.MonoidHom.map_closedLowerCentralSeries_eq_of_surjective (f : G →* H)
    (hf : Continuous f) (hfc : IsClosedMap f) (hsurj : Function.Surjective f) (n : ℕ) :
    (closedLowerCentralSeries G n).map f = closedLowerCentralSeries H n := by
  simp only [closedLowerCentralSeries_def]
  exact f.map_pLowerCentralSeries_eq_of_surjective hf hfc hsurj n

/-- A topological group isomorphism matches the closed lower central series of its source and
target term by term. -/
theorem _root_.ContinuousMulEquiv.map_closedLowerCentralSeries_eq (e : G ≃ₜ* H) (n : ℕ) :
    (closedLowerCentralSeries G n).map e.toMulEquiv.toMonoidHom = closedLowerCentralSeries H n := by
  simp only [closedLowerCentralSeries_def]
  exact e.map_pLowerCentralSeries_eq n

variable (G) in
/-- Every term of the closed lower central series is topologically characteristic. -/
theorem isTopCharacteristic_closedLowerCentralSeries (n : ℕ) :
    IsTopCharacteristic G (closedLowerCentralSeries G n) := by
  rw [closedLowerCentralSeries_def]
  exact isTopCharacteristic_pLowerCentralSeries 0 n

end TauCeti
