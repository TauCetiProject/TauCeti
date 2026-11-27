/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The pullback of a set of covectors

Let `f : E → E'` be a map between real inner product spaces, `U` a subset of `E` and `Γ` a set of
covectors `(y, η) ∈ E' × E'`. The pullback

`f^* Γ = {(x, Df(x)ᵀ η) | x ∈ U, (f x, η) ∈ Γ}` (`TauCeti.covectorPullback f U Γ`)

pulls the covectors over `f x` back to `x` by the transpose of the derivative of `f` at `x`. It
bounds the wave front set of the pullback of a distribution along a smooth map
(Hörmander I, Theorem 8.2.4): `WF(f^* T) ⊆ f^* WF(T)`. It is monotone in `Γ`, and it is a cone
whenever `Γ` is one.

When the transposed derivatives `Df(x)ᵀ` are injective, `f^* Γ` contains no zero covector if `Γ`
contains none. If moreover they have left inverses `L x` depending continuously on `x`, then
`f^* Γ` is closed in `U × (E \ {0})` whenever `Γ` is closed in `Ω' × (E' \ {0})`: a covector `ζ`
over `x` lies in `f^* Γ` exactly when `Df(x)ᵀ (L x ζ) = ζ` and `(f x, L x ζ) ∈ Γ`.

## Main declarations

* `TauCeti.covectorPullback`: the pullback `f^* Γ` of a set of covectors.
* `TauCeti.mem_covectorPullback`, `TauCeti.covectorPullback_mono`,
  `TauCeti.smul_mem_covectorPullback`: its membership, its monotonicity in `Γ` and its invariance
  under positive scalings of covectors.
* `TauCeti.ne_zero_of_mem_covectorPullback`: for injective transposed derivatives, `f^* Γ`
  contains no zero covector if `Γ` contains none.
* `TauCeti.isOpen_diff_covectorPullback_of_leftInverse`: for transposed derivatives with
  continuous left inverses, `f^* Γ` is closed in `U × (E \ {0})` if `Γ` is closed in
  `Ω' × (E' \ {0})`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 8.2.4.
-/

public section

open Function Set
open scoped InnerProduct

namespace TauCeti

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [CompleteSpace E']

/-- The pullback `f^* Γ = {(x, Df(x)ᵀ η) | x ∈ U, (f x, η) ∈ Γ}` of a set `Γ` of covectors along a
map `f` over a set `U`: covectors over `f x` pull back by the transpose of the derivative of `f`
at `x`. -/
def covectorPullback (f : E → E') (U : Set E) (Γ : Set (E' × E')) : Set (E × E) :=
  {p | p.1 ∈ U ∧ ∃ η, (f p.1, η) ∈ Γ ∧ ((fderiv ℝ f p.1)†) η = p.2}

@[simp]
theorem mem_covectorPullback {f : E → E'} {U : Set E} {Γ : Set (E' × E')} {p : E × E} :
    p ∈ covectorPullback f U Γ ↔ p.1 ∈ U ∧ ∃ η, (f p.1, η) ∈ Γ ∧ ((fderiv ℝ f p.1)†) η = p.2 :=
  Iff.rfl

theorem covectorPullback_mono {f : E → E'} {U : Set E} {Γ Γ' : Set (E' × E')} (h : Γ ⊆ Γ') :
    covectorPullback f U Γ ⊆ covectorPullback f U Γ' :=
  fun _ ⟨hx, η, hη, hp⟩ ↦ ⟨hx, η, h hη, hp⟩

/-- The pullback of a cone is a cone. -/
theorem smul_mem_covectorPullback {f : E → E'} {U : Set E} {Γ : Set (E' × E')}
    (hcone : ∀ p ∈ Γ, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ Γ) {p : E × E}
    (hp : p ∈ covectorPullback f U Γ) {t : ℝ} (ht : 0 < t) :
    (p.1, t • p.2) ∈ covectorPullback f U Γ := by
  obtain ⟨hx, η, hη, hηp⟩ := hp
  exact ⟨hx, t • η, hcone _ hη t ht, by rw [map_smul, hηp]⟩

/-- If the transposed derivatives of `f` are injective over `U`, the pullback of a set of nonzero
covectors contains no zero covector. -/
theorem ne_zero_of_mem_covectorPullback {f : E → E'} {U : Set E} {Γ : Set (E' × E')}
    (hinj : ∀ x ∈ U, Injective ((fderiv ℝ f x)†)) (hΓ0 : ∀ p ∈ Γ, p.2 ≠ 0) {p : E × E}
    (hp : p ∈ covectorPullback f U Γ) : p.2 ≠ 0 := by
  obtain ⟨hx, η, hη, hηp⟩ := hp
  rw [← hηp]
  exact (map_ne_zero_iff _ (hinj _ hx)).2 (hΓ0 _ hη)

/-- **The pullback of a closed cone is closed.** Let `f` be continuous with continuous derivative
on an open set `U`, mapping `U` into `Ω'`, and let the transposed derivatives `Df(x)ᵀ` have left
inverses `L x` depending continuously on `x ∈ U`. If `Γ` is closed in `Ω' × (E' \ {0})`, then
`f^* Γ` is closed in `U × (E \ {0})`. -/
theorem isOpen_diff_covectorPullback_of_leftInverse {f : E → E'} {U : Set E} {Ω' : Set E'}
    {Γ : Set (E' × E')} (hU : IsOpen U) (hfU : MapsTo f U Ω') (hf : ContinuousOn f U)
    (hDf : ContinuousOn (fderiv ℝ f) U) (L : E → E →L[ℝ] E') (hL : ContinuousOn L U)
    (hLinv : ∀ x ∈ U, ∀ η, L x (((fderiv ℝ f x)†) η) = η) (hΓ : IsOpen ((Ω' ×ˢ {0}ᶜ) \ Γ)) :
    IsOpen ((U ×ˢ {0}ᶜ) \ covectorPullback f U Γ) := by
  set S : Set (E × E) := U ×ˢ {0}ᶜ
  have hS : IsOpen S := hU.prod isOpen_compl_singleton
  have hU₁ : MapsTo Prod.fst S U := fun _ hq ↦ hq.1
  -- The candidate `L x ζ` for the covector `η` with `Df(x)ᵀ η = ζ`, continuous over `S`.
  have hLζ : ContinuousOn (fun q : E × E ↦ L q.1 q.2) S :=
    (hL.comp continuous_fst.continuousOn hU₁).clm_apply continuous_snd.continuousOn
  have hDLζ : ContinuousOn (fun q : E × E ↦ ((fderiv ℝ f q.1)†) (L q.1 q.2)) S :=
    (((ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := E) (F := E')).continuous.comp_continuousOn
      (hDf.comp continuous_fst.continuousOn hU₁)).clm_apply hLζ)
  -- Off `f^* Γ`, either `ζ` is not in the range of `Df(x)ᵀ`, or `(f x, L x ζ) ∉ Γ`.
  have hset : S \ covectorPullback f U Γ =
      (S ∩ (fun q : E × E ↦ (q.2, ((fderiv ℝ f q.1)†) (L q.1 q.2))) ⁻¹' (diagonal E)ᶜ) ∪
        (S ∩ (fun q : E × E ↦ (f q.1, L q.1 q.2)) ⁻¹' ((Ω' ×ˢ {0}ᶜ) \ Γ)) := by
    ext ⟨x, ζ⟩
    simp only [S, mem_sdiff, mem_prod, mem_compl_iff, mem_singleton_iff, mem_inter_iff,
      mem_union, mem_preimage, mem_diagonal_iff, mem_covectorPullback, not_and, not_exists]
    constructor
    · rintro ⟨⟨hx, hζ⟩, hnot⟩
      by_cases h : ζ = ((fderiv ℝ f x)†) (L x ζ)
      · refine Or.inr ⟨⟨hx, hζ⟩, ⟨hfU hx, fun h0 ↦ hζ ?_⟩, fun hmem ↦ hnot hx _ hmem h.symm⟩
        rw [h, h0, map_zero]
      · exact Or.inl ⟨⟨hx, hζ⟩, h⟩
    · rintro (⟨⟨hx, hζ⟩, h⟩ | ⟨⟨hx, hζ⟩, -, h⟩) <;>
        refine ⟨⟨hx, hζ⟩, fun _ η hη hηζ ↦ ?_⟩ <;> subst hηζ <;> rw [hLinv x hx η] at h
      · exact h rfl
      · exact h hη
  rw [hset]
  exact ((continuous_snd.continuousOn.prodMk hDLζ).isOpen_inter_preimage hS
    isClosed_diagonal.isOpen_compl).union
    (((hf.comp continuous_fst.continuousOn hU₁).prodMk hLζ).isOpen_inter_preimage hS hΓ)

end TauCeti
