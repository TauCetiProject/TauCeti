/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ImplicitAtlas.LocallyOrientable.Basic
public import TauCeti.Topology.ImplicitAtlas.Prod
import TauCeti.AlgebraicTopology.Singular.LocalHomology.Prod

/-!
# Local orientability of product atlases

Let `𝒜₁` and `𝒜₂` be implicit atlases on `X₁` and `X₂`, and `𝒜₁.prod 𝒜₂` their product on
`X₁ × X₂` (`TauCeti.ImplicitAtlas.prod`, Pardon, Definition 6.3.1). At a finite set `I` of indices
in `A₁ ⊕ A₂` with left and right parts `I₁` and `I₂`, the product atlas has the thickening
`X₁_(I₁) × X₂_(I₂)`, on which `Γ_I = Γ₁_(I₁) × Γ₂_(I₂)` acts factorwise, and the obstruction space
`E_I = E₁_(I₁) × E₂_(I₂)`. This file proves that the product of locally orientable atlases is
locally orientable (`TauCeti.ImplicitAtlas.IsLocallyOrientable.prod`), as Pardon's product of
virtual fundamental classes requires.

At a regular zero `x = (x₁, x₂)` of `X_I`, an element `g = (g₁, g₂)` fixing `x` fixes `x₁` and `x₂`,
which are regular zeros of the factors, so by local orientability of the factors `gᵢ` acts on the
local orientation line `oᵢ` of `Xᵢ_(Iᵢ)` at `xᵢ` by the sign `εᵢ` of the determinant of its action
on `Eᵢ_(Iᵢ)`. The two signs multiply on both sides.

* **On the local orientation line.** Every regular point `xᵢ` of a factor has a chart of the
  thickening `Xᵢ_(Iᵢ)` to `ℝ^(dᵢ + m_Iᵢ)`
  (`TauCeti.ImplicitAtlas.exists_openPartialHomeomorph_of_mem_regLocus`), so the product map
  `g₁ × g₂` acts on the local orientation line of `X₁_(I₁) × X₂_(I₂)` at `(x₁, x₂)` by `ε₁ ε₂`
  (`TauCeti.localHomologyMap_uliftInt_prodMap_eq_smul`, through the Künneth map of local
  homology).
* **On the obstruction space.** The determinant of `g` on `E_I` is the product of the determinants
  of `g₁` on `E₁_(I₁)` and of `g₂` on `E₂_(I₂)`
  (`TauCeti.ImplicitAtlas.det_externalPi_sumElimRep`).

The local homology of the thickenings is taken with integral coefficients `ULift ℤ`, as in
`TauCeti.ImplicitAtlas.IsLocallyOrientable`, and the Künneth theorem is applied with coefficients
`ℤ`; since its coefficient ring lives in the universe of the spaces, the thickenings of the two
factors are taken in `Type`.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), 779–1034, Definition 4.1.2 (locally
  orientable implicit atlases) and Definition 6.3.1 (product implicit atlases).
-/

public section

open CategoryTheory Finset

namespace TauCeti.ImplicitAtlas

universe u v

variable {A₁ A₂ : Type*} [DecidableEq A₁] [DecidableEq A₂]
  {Γ₁ : A₁ → Type u} [∀ a, Group (Γ₁ a)] [∀ a, Finite (Γ₁ a)]
  {E₁ : A₁ → Type v} [∀ a, NormedAddCommGroup (E₁ a)] [∀ a, NormedSpace ℝ (E₁ a)]
  [∀ a, FiniteDimensional ℝ (E₁ a)] {ρ₁ : ∀ a, Representation ℝ (Γ₁ a) (E₁ a)}
  {Γ₂ : A₂ → Type u} [∀ b, Group (Γ₂ b)] [∀ b, Finite (Γ₂ b)]
  {E₂ : A₂ → Type v} [∀ b, NormedAddCommGroup (E₂ b)] [∀ b, NormedSpace ℝ (E₂ b)]
  [∀ b, FiniteDimensional ℝ (E₂ b)] {ρ₂ : ∀ b, Representation ℝ (Γ₂ b) (E₂ b)}

omit [DecidableEq A₁] [DecidableEq A₂] [∀ a, Finite (Γ₁ a)] [∀ b, Finite (Γ₂ b)] in
/-- **Determinants on the obstruction space of a product atlas.** An element `g` of
`Γ_I = ∏_(α ∈ I) Γ_α`, for a finite `I ⊆ A₁ ⊕ A₂`, acts on `E_I` with determinant the product of
the determinants of its left part on `E₁_(I.toLeft)` and of its right part on `E₂_(I.toRight)`. -/
theorem det_externalPi_sumElimRep (I : Finset (A₁ ⊕ A₂)) (g : (α : I) → Sum.elim Γ₁ Γ₂ α) :
    LinearMap.det (Representation.externalPi (fun α : I ↦ sumElimRep ρ₁ ρ₂ α) g) =
      LinearMap.det (Representation.externalPi (fun a : I.toLeft ↦ ρ₁ a)
          ((Equiv.piFinsetSum (Sum.elim Γ₁ Γ₂) I I.toLeft I.toRight) g).1) *
        LinearMap.det (Representation.externalPi (fun b : I.toRight ↦ ρ₂ b)
          ((Equiv.piFinsetSum (Sum.elim Γ₁ Γ₂) I I.toLeft I.toRight) g).2) := by
  -- The indices of `I` are its left indices and its right indices.
  let e : I ≃ I.toLeft ⊕ I.toRight := Equiv.subtypeSum.trans
    (Equiv.sumCongr (Equiv.subtypeEquivRight fun _ ↦ mem_toLeft.symm)
      (Equiv.subtypeEquivRight fun _ ↦ mem_toRight.symm))
  let p := (Equiv.piFinsetSum (Sum.elim Γ₁ Γ₂) I I.toLeft I.toRight) g
  -- The left and right parts `p` of `g` act on the factors of `E_I` through `ρ₁` and `ρ₂`. The
  -- equalities are stated as terms since `Sum.elim Γ₁ Γ₂ (.inl a)` is `Γ₁ a` only up to unfolding.
  exact (Representation.det_externalPi _ _).trans <|
    (Fintype.prod_equiv e _ (Sum.elim (fun a ↦ LinearMap.det (ρ₁ a (p.1 a)))
      (fun b ↦ LinearMap.det (ρ₂ b (p.2 b))))
      (by rintro ⟨a | b, h⟩ <;> simp only [sumElimRep_inl, sumElimRep_inr] <;> rfl)).trans <|
    (Fintype.prod_sum_type _).trans <|
    congrArg₂ (· * ·) (Representation.det_externalPi _ _).symm
      (Representation.det_externalPi _ _).symm

variable {T₁ : Finset A₁ → Type} [∀ I, TopologicalSpace (T₁ I)] [∀ I, T2Space (T₁ I)]
  {act₁ : ∀ I : Finset A₁, ((a : I) → Γ₁ a) →* (T₁ I ≃ₜ T₁ I)}
  {X₁ : Type*} [TopologicalSpace X₁] {d₁ : ℤ}
  {T₂ : Finset A₂ → Type} [∀ I, TopologicalSpace (T₂ I)] [∀ I, T2Space (T₂ I)]
  {act₂ : ∀ I : Finset A₂, ((b : I) → Γ₂ b) →* (T₂ I ≃ₜ T₂ I)}
  {X₂ : Type*} [TopologicalSpace X₂] {d₂ : ℤ}

/-- **The product of locally orientable atlases is locally orientable.** If the implicit atlases
`𝒜₁` and `𝒜₂`, whose thickenings are in `Type`, are locally orientable, then so is their product
`𝒜₁.prod 𝒜₂` on `X₁ × X₂`. -/
theorem IsLocallyOrientable.prod {𝒜₁ : ImplicitAtlas Γ₁ E₁ ρ₁ T₁ act₁ X₁ d₁}
    {𝒜₂ : ImplicitAtlas Γ₂ E₂ ρ₂ T₂ act₂ X₂ d₂} (h₁ : 𝒜₁.IsLocallyOrientable)
    (h₂ : 𝒜₂.IsLocallyOrientable) : (𝒜₁.prod 𝒜₂).IsLocallyOrientable := by
  refine isLocallyOrientable_iff.2 fun I x hx hx₀ g hg n hn ↦ ?_
  set e := Equiv.piFinsetSum (Sum.elim Γ₁ Γ₂) I I.toLeft I.toRight
  -- The point `x` is a pair of regular zeros, fixed by the left and right parts of `g`.
  rw [toCore_prod, Core.regLocus_prod] at hx
  rw [toCore_prod, Core.kuranishiZeroSet_prod] at hx₀
  have hg' := Prod.ext_iff.1 hg
  rw [prodAct_apply] at hg'
  obtain ⟨n₁, hn₁, φ₁, hx₁⟩ := 𝒜₁.exists_openPartialHomeomorph_of_mem_regLocus hx.1
  obtain ⟨n₂, hn₂, φ₂, hx₂⟩ := 𝒜₂.exists_openPartialHomeomorph_of_mem_regLocus hx.2
  -- The expected dimensions add.
  obtain rfl : n = n₁ + n₂ := by
    have hsum : ∑ α ∈ I, (Module.finrank ℝ (Sum.elim E₁ E₂ α) : ℤ) =
        ∑ a ∈ I.toLeft, (Module.finrank ℝ (E₁ a) : ℤ) +
          ∑ b ∈ I.toRight, (Module.finrank ℝ (E₂ b) : ℤ) :=
      Finset.sum_sum_eq_sum_toLeft_add_sum_toRight _ _
    omega
  -- The action of `g` is the product of the actions of its two parts.
  have hmap : ((prodAct act₁ act₂ I g : _ ≃ₜ _) : C(_, _)) =
      (act₁ I.toLeft (e g).1 : C(T₁ I.toLeft, T₁ I.toLeft)).prodMap
        (act₂ I.toRight (e g).2 : C(T₂ I.toRight, T₂ I.toRight)) :=
    ContinuousMap.ext fun p ↦ prodAct_apply act₁ act₂ I g p
  -- The sign of the determinant of `g` is the product of the signs of its two parts.
  have hdet := (congrArg (fun r : ℝ ↦ ((SignType.sign r : SignType) : ℤ))
    (det_externalPi_sumElimRep (ρ₁ := ρ₁) (ρ₂ := ρ₂) I g)).trans
      ((congrArg (fun s : SignType ↦ (s : ℤ)) (sign_mul _ _)).trans (SignType.coe_mul _ _))
  -- The two parts act on the local orientation lines of the factors by their determinant signs.
  rw [localHomologyMap_congr _ hmap, hdet]
  exact localHomologyMap_uliftInt_prodMap_eq_smul φ₁ hx₁ φ₂ hx₂ finrank_euclideanSpace_fin
    finrank_euclideanSpace_fin _ _ _ (h₁.localHomologyMap_eq hx.1 hx₀.1 hg'.1 hn₁)
    (h₂.localHomologyMap_eq hx.2 hx₀.2 hg'.2 hn₂)

end TauCeti.ImplicitAtlas
