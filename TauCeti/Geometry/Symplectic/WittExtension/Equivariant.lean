/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Semisimple
public import TauCeti.Geometry.Symplectic.Lagrangian.CoisotropicModel
public import TauCeti.Geometry.Symplectic.LinearReduction
public import TauCeti.Geometry.Symplectic.Prod.Basic
public import TauCeti.LinearAlgebra.BilinearForm.Isometry.Ker
import TauCeti.Geometry.Symplectic.Invariants
import TauCeti.RepresentationTheory.Subrepresentation

/-!
# The equivariant presymplectic Witt extension

Let a group `H` act linearly on a finite-dimensional real symplectic vector space `(E, ω)` by
symplectomorphisms, `ρ : H →* (E ≃ₗ E)`, and let `ι : W → E` be an injective, `H`-equivariant
linear map from a representation `ρ_W` of `H` on `W`, pulling `ω` back to an alternating form `B`.
Put `K = ker B`, so that `ι` carries `K` onto the radical `ι W ∩ (ι W)^ω`, and let
`V = (ι W)^ω ⧸ (ι W ∩ (ι W)^ω)` be the reduced space of `(ι W)^ω`, the *symplectic normal space*,
with its reduced symplectic form `ω_V` and the induced action of `H`
(`TauCeti.SymplecticForm.reducedSpaceRepresentation`).

The group acts on `K` by restricting `ρ_W` (`LinearMap.BilinForm.kerRepresentation`), and on the
dual `K*` by the contragredient action `a ↦ a ∘ ρ_W(h⁻¹)`
(`LinearMap.BilinForm.kerDualRepresentation`). For a projection `P : W → K` (`P k = k` on `K`)
which is `H`-equivariant, the linear coisotropic model form on `W × K*`,

`((w, a), (w', a')) ↦ B(w, w') + a'(P w) - a(P w')`

(`LinearMap.BilinForm.IsAlt.coisotropicModel`), is invariant under the product action
(`LinearMap.BilinForm.IsAlt.isSymplectomorphism_coisotropicModel_prodCongr`).

The main theorem is the **equivariant presymplectic Witt extension**
(`LinearMap.BilinForm.IsAlt.exists_equivariant_isSymplectomorphism_coisotropicModel_prod`):
if the representation of `H` on `E` is semisimple, for instance a continuous representation of a
compact group (`Representation.isSemisimpleRepresentation_of_continuous`), then `ι` extends to an
`H`-equivariant linear symplectomorphism

`(W × K*) × V ≃ E`, `((w, 0), 0) ↦ ι w`,

from the direct sum of the coisotropic model and `(V, ω_V)`, which maps each `((0, 0), v)` into
`(ι W)^ω` with class `v` in `V`. This is the linear part of the
Marle–Guillemin–Sternberg local normal form of a Hamiltonian action near an orbit through `p`:
there `W` is the orbit tangent space `𝔤 ⧸ 𝔤_p`, `H = G_p` is the stabilizer,
`K ≅ 𝔤_{μ(p)} ⧸ 𝔤_p`, `V` is the symplectic slice, and the tangent space of the model
`G ×_H (𝔪* × V)` at its base point is `W × K* × V` with a form of this shape. Without equivariance
the statement follows from Witt's extension theorem
(`TauCeti.SymplecticForm.exists_isSymplectomorphism_extend`); the point here is that every choice
in the construction can be made `H`-invariantly.

The extension is `((w, a), v) ↦ ι w + ℓ a + s v`. Here `s : V → (ι W)^ω` is the equivariant section
of the quotient map with image an invariant complement of the radical. The map `ℓ : K* → E` is
first chosen, in an invariant complement of the symplectic orthogonal of `ι W + s V`, with
`ω(ι w + s v, ℓ a) = a(P w)`; its image need not be isotropic, and it is corrected by
`ℓ a ↦ ℓ a + ι κ a`, where `κ : K* → K` is defined by `a'(κ a) = -½ ω(ℓ a, ℓ a')`, which makes the
image isotropic and keeps the other pairings. Semisimplicity supplies the invariant complements,
and uniqueness of the defining linear conditions gives the equivariance of `s`, `ℓ` and `κ`.

Semisimplicity cannot be dropped: the shear `(q, p) ↦ (q + p, p)` of `ℝ²` generates a symplectic
action of `ℤ` fixing the Lagrangian line `W = ℝ × 0`, on which `B = 0`, `K = W` and `V = 0`; the
model `W × W*` then carries the trivial action, which is not conjugate to the shear.

## Main results

* `TauCeti.SymplecticForm.exists_equivariant_section_reducedSpace`: for a semisimple symplectic
  representation, the quotient map of an invariant subspace onto its reduced space has an
  equivariant linear section.
* `LinearMap.BilinForm.IsAlt.isSymplectomorphism_coisotropicModel_prodCongr`: for an equivariant
  projection, the group acts on the coisotropic model by symplectomorphisms.
* `LinearMap.BilinForm.IsAlt.exists_equivariant_isSymplectomorphism_coisotropicModel_prod`:
  the equivariant presymplectic Witt extension.

## References

* C.-M. Marle, *Modèle d'action hamiltonienne d'un groupe de Lie sur une variété symplectique*,
  Rend. Sem. Mat. Univ. Politec. Torino 43 (1985), 227–251.
* V. Guillemin and S. Sternberg, *A normal form for the moment map*, in *Differential Geometric
  Methods in Mathematical Physics*, Reidel, 1984, 161–175.
* J.-P. Ortega and T. S. Ratiu, *Momentum Maps and Hamiltonian Reduction*, Birkhäuser, 2004,
  Sections 7.1–7.2 (the symplectic slice and the linear model).
-/

public section

open Module TauCeti TauCeti.SymplecticForm

namespace LinearMap.BilinForm.IsAlt

variable {H W : Type*} [Group H] [AddCommGroup W] [Module ℝ W] {B : LinearMap.BilinForm ℝ W}
  (hB : B.IsAlt) {P : W →ₗ[ℝ] LinearMap.ker B} (hP : ∀ k : LinearMap.ker B, P k = k)
  {ρ : H →* W ≃ₗ[ℝ] W} (hρ : ∀ h, B.IsOrthogonal (ρ h))

/-- For a projection `P` of `W` onto the kernel `K` of `B` which commutes with the action of `H`,
each `h ∈ H` acts on the coisotropic model `W × K*` by a symplectomorphism, through `ρ h` on `W`
and the contragredient action on `K*`. -/
theorem isSymplectomorphism_coisotropicModel_prodCongr
    (hPρ : ∀ h w, P (ρ h w) = B.kerRepresentation ρ hρ h (P w)) (h : H) :
    IsSymplectomorphism (hB.coisotropicModel P hP) (hB.coisotropicModel P hP)
      ((ρ h).prodCongr (B.kerDualRepresentation ρ hρ h)) := by
  rw [isSymplectomorphism_iff]
  rintro ⟨w, a⟩ ⟨w', a'⟩
  simp [hPρ, hρ h w w']

end LinearMap.BilinForm.IsAlt

/-! ### Invariant choices in a semisimple symplectic representation -/

namespace TauCeti.SymplecticForm

variable {H E : Type*} [Group H] [AddCommGroup E] [Module ℝ E] {ω : SymplecticForm E}
  {ρ : H →* E ≃ₗ[ℝ] E}

/-- `IsSymplectomorphism.apply`, with the form written through `toBilinForm`. -/
private theorem isSymplectomorphism_toBilinForm_apply {e : E ≃ₗ[ℝ] E}
    (he : IsSymplectomorphism ω ω e) (u u' : E) :
    ω.toBilinForm (e u) (e u') = ω.toBilinForm u u' :=
  he.apply u u'

/-- For a semisimple representation by symplectomorphisms, the quotient map of an invariant
subspace `U` onto its reduced space has an equivariant linear section, whose image is an invariant
complement of the radical `U ∩ U^ω` in `U`. -/
theorem exists_equivariant_section_reducedSpace
    [Representation.IsSemisimpleRepresentation
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ)]
    (hρ : ∀ h, IsSymplectomorphism ω ω (ρ h)) {U : Submodule ℝ E}
    (hU : ∀ h, ∀ u ∈ U, ρ h u ∈ U) :
    ∃ s : ω.ReducedSpace U →ₗ[ℝ] U, (∀ v, Submodule.Quotient.mk (s v) = v) ∧
      ∀ h v, (s (ω.reducedSpaceRepresentation ρ hρ U hU h v) : E) = ρ h (s v) := by
  -- An invariant complement `C` of the radical `U ∩ U^ω` in `E`.
  obtain ⟨C, hC⟩ := exists_isCompl
    (⟨U ⊓ ω.orthogonal U, fun h x hx ↦ ⟨hU h x hx.1, apply_mem_orthogonal
      (ρ := LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ)
      (fun g u v ↦ (hρ g).apply u v) hU h hx.2⟩⟩ :
      Subrepresentation (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ))
  -- Its trace on `U` is a complement of the kernel of `ω|_U`.
  have hpq : IsCompl (LinearMap.ker (ω.toBilinForm.restrict U))
      (C.toSubmodule.comap U.subtype) := by
    convert Submodule.isCompl_comap_subtype_of_isCompl_of_le
      (Subrepresentation.isCompl_toSubmodule.2 hC) (inf_le_left : U ⊓ ω.orthogonal U ≤ U) using 1
    ext u
    rw [mem_ker_restrict_iff]
    simp
  let e := Submodule.quotientEquivOfIsCompl _ _ hpq
  refine ⟨Submodule.subtype _ ∘ₗ e.toLinearMap,
    fun v ↦ Submodule.mk_quotientEquivOfIsCompl_apply hpq v, fun h v ↦ ?_⟩
  -- `ρ h (s v)` lies in the complement and has class `h • v`, so it is `s (h • v)`.
  let y : C.toSubmodule.comap U.subtype :=
    ⟨⟨ρ h (e v), hU h _ (e v : U).2⟩, C.apply_mem_toSubmodule h (e v).2⟩
  have hv : ω.reducedSpaceRepresentation ρ hρ U hU h v = Submodule.Quotient.mk (y : U) := by
    conv_lhs => rw [← Submodule.mk_quotientEquivOfIsCompl_apply hpq v]
    rw [reducedSpaceRepresentation_apply_mk]
  have hy : e (ω.reducedSpaceRepresentation ρ hρ U hU h v) = y := by
    rw [hv]
    exact Submodule.quotientEquivOfIsCompl_apply_mk_right hpq y
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, hy]
  simp [y]

/-- For an injective linear map `f` with invariant image, there is a linear map `L : X* → E`
with `ω (f x) (L φ) = φ x`, with values in an invariant subspace `D` on which pairing against the
image of `f` is injective. -/
private theorem exists_dual_lift [FiniteDimensional ℝ E]
    [Representation.IsSemisimpleRepresentation
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ)]
    (hρ : ∀ h, IsSymplectomorphism ω ω (ρ h)) {X : Type*} [AddCommGroup X] [Module ℝ X]
    {f : X →ₗ[ℝ] E} (hf : Function.Injective f)
    (hfρ : ∀ h, ∀ y ∈ LinearMap.range f, ρ h y ∈ LinearMap.range f) :
    ∃ (L : Dual ℝ X →ₗ[ℝ] E) (D : Submodule ℝ E), (∀ φ x, ω (f x) (L φ) = φ x) ∧
      (∀ φ, L φ ∈ D) ∧ (∀ h, ∀ y ∈ D, ρ h y ∈ D) ∧
      ∀ y ∈ D, (∀ x, ω (f x) y = 0) → y = 0 := by
  have : FiniteDimensional ℝ X := .of_injective f hf
  -- An invariant complement `D` of `(range f)^ω`.
  obtain ⟨D, hD⟩ := exists_isCompl
    (⟨ω.orthogonal (LinearMap.range f), fun h x hx ↦ apply_mem_orthogonal
      (ρ := LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ)
      (fun g u v ↦ (hρ g).apply u v) hfρ h hx⟩ :
      Subrepresentation (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ))
  replace hD := Subrepresentation.isCompl_toSubmodule.2 hD
  -- Pairing against the image of `f` identifies `D` with `X*`.
  let Ψ : D.toSubmodule →ₗ[ℝ] Dual ℝ X :=
    f.dualMap ∘ₗ ω.toBilinForm.flip ∘ₗ D.toSubmodule.subtype
  have hΨ (y : D.toSubmodule) (x : X) : Ψ y x = ω (f x) y := rfl
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    have hy' : (y : E) ∈ ω.orthogonal (LinearMap.range f) := by
      rw [mem_orthogonal_iff]
      rintro _ ⟨x, rfl⟩
      simpa [hΨ] using LinearMap.congr_fun (LinearMap.mem_ker.1 hy) x
    exact Subtype.ext ((Submodule.disjoint_def.1 hD.disjoint) _ hy' y.2)
  have hdim : finrank ℝ D.toSubmodule = finrank ℝ (Dual ℝ X) := by
    have h₁ : finrank ℝ (ω.orthogonal (LinearMap.range f)) + finrank ℝ D.toSubmodule =
        finrank ℝ E :=
      Submodule.finrank_add_eq_of_isCompl hD
    have h₂ := ω.finrank_add_finrank_orthogonal (LinearMap.range f)
    rw [Subspace.dual_finrank_eq, ← LinearMap.finrank_range_of_inj hf]
    omega
  let Ψe := Ψ.linearEquivOfInjective hinj hdim
  refine ⟨D.toSubmodule.subtype ∘ₗ Ψe.symm.toLinearMap, D.toSubmodule, fun φ x ↦ ?_,
    fun φ ↦ (Ψe.symm φ).2, fun h y hy ↦ D.apply_mem_toSubmodule h hy, fun y hy h₀ ↦ ?_⟩
  · rw [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply, ← hΨ]
    exact LinearMap.congr_fun (Ψe.apply_symm_apply φ) x
  · have : Ψ ⟨y, hy⟩ = Ψ 0 := LinearMap.ext fun x ↦ by simpa [hΨ] using h₀ x
    simpa using hinj this

end TauCeti.SymplecticForm

/-! ### The equivariant extension -/

namespace LinearMap.BilinForm.IsAlt

variable {H W E : Type*} [Group H] [AddCommGroup W] [Module ℝ W] [AddCommGroup E] [Module ℝ E]
  [FiniteDimensional ℝ E] {B : LinearMap.BilinForm ℝ W} {P : W →ₗ[ℝ] LinearMap.ker B}
  {ρW : H →* W ≃ₗ[ℝ] W} {ω : SymplecticForm E} {ρ : H →* E ≃ₗ[ℝ] E} {ι : W →ₗ[ℝ] E}
  [Representation.IsSemisimpleRepresentation
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ)]
  {V : Type*} [AddCommGroup V] [Module ℝ V] {σ : H →* V ≃ₗ[ℝ] V} {s : V →ₗ[ℝ] E}

/-- An equivariant `ℓ : K* → E` with `ω (ι w + s v) (ℓ a) = a (P w)`, for an equivariant
`s : V → E` such that `(w, v) ↦ ι w + s v` is injective. -/
private theorem exists_lift_pairing (hρW : ∀ h, B.IsOrthogonal (ρW h))
    (hPρ : ∀ h w, P (ρW h w) = B.kerRepresentation ρW hρW h (P w))
    (hρ : ∀ h, IsSymplectomorphism ω ω (ρ h)) (hιρ : ∀ h w, ι (ρW h w) = ρ h (ι w))
    (hsρ : ∀ h v, s (σ h v) = ρ h (s v)) (hf : Function.Injective (ι.coprod s)) :
    ∃ ℓ : Dual ℝ (LinearMap.ker B) →ₗ[ℝ] E, (∀ a w v, ω (ι w + s v) (ℓ a) = a (P w)) ∧
      ∀ h a, ℓ (B.kerDualRepresentation ρW hρW h a) = ρ h (ℓ a) := by
  obtain ⟨L, D, hL, hLD, hD, hD₀⟩ := TauCeti.SymplecticForm.exists_dual_lift hρ hf (by
    rintro h _ ⟨⟨w, v⟩, rfl⟩
    exact ⟨(ρW h w, σ h v), by simp [hιρ, hsρ]⟩)
  beta_reduce at hL hD₀
  refine ⟨L ∘ₗ (P ∘ₗ LinearMap.fst ℝ W V).dualMap,
    fun a w v ↦ ?_, fun h a ↦ ?_⟩
  · have := hL ((P ∘ₗ LinearMap.fst ℝ W V).dualMap a) (w, v)
    rwa [LinearMap.dualMap_apply, LinearMap.comp_apply, LinearMap.fst_apply,
      LinearMap.coprod_apply] at this
  -- Both sides lie in `D` and pair in the same way with the image of `ι.coprod s`.
  rw [← sub_eq_zero]
  refine hD₀ _ (D.sub_mem (hLD _) (hD h _ (hLD _))) fun ⟨w, v⟩ ↦ ?_
  have hx : ι.coprod s (w, v) = ρ h (ι.coprod s (ρW h⁻¹ w, σ h⁻¹ v)) := by
    rw [LinearMap.coprod_apply, LinearMap.coprod_apply, map_add, ← hιρ, ← hsρ]
    simp
  have hPρ' (w : W) : P ((ρW h).symm w) = (B.kerRepresentation ρW hρW h).symm (P w) := by
    rw [LinearEquiv.eq_symm_apply, ← hPρ, LinearEquiv.apply_symm_apply]
  rw [LinearMap.comp_apply, LinearMap.comp_apply, map_sub, hL, hx,
    isSymplectomorphism_toBilinForm_apply (hρ h), hL, sub_eq_zero]
  simp [LinearMap.dualMap_apply', hPρ']

/-- An equivariant `ℓ : K* → E` with isotropic image, `ω`-orthogonal to the image of `s`, and with
`ω (ι w) (ℓ a) = a (P w)`. It corrects the lift of `exists_lift_pairing` by `ι ∘ κ`, where
`a' (κ a) = -½ ω (ℓ a) (ℓ a')`. -/
private theorem exists_isotropic_lift (hB : B.IsAlt) (hP : ∀ k : LinearMap.ker B, P k = k)
    (hρW : ∀ h, B.IsOrthogonal (ρW h))
    (hPρ : ∀ h w, P (ρW h w) = B.kerRepresentation ρW hρW h (P w))
    (hρ : ∀ h, IsSymplectomorphism ω ω (ρ h)) (hι : Function.Injective ι)
    (hω : ∀ w w', ω (ι w) (ι w') = B w w') (hιρ : ∀ h w, ι (ρW h w) = ρ h (ι w))
    (hsι : ∀ w v, ω (ι w) (s v) = 0) (hsρ : ∀ h v, s (σ h v) = ρ h (s v))
    (hf : Function.Injective (ι.coprod s)) :
    ∃ ℓ : Dual ℝ (LinearMap.ker B) →ₗ[ℝ] E, (∀ a w, ω (ι w) (ℓ a) = a (P w)) ∧
      (∀ a v, ω (s v) (ℓ a) = 0) ∧ (∀ a a', ω (ℓ a) (ℓ a') = 0) ∧
      ∀ h a, ℓ (B.kerDualRepresentation ρW hρW h a) = ρ h (ℓ a) := by
  have : FiniteDimensional ℝ W := .of_injective ι hι
  obtain ⟨ℓ₀, hℓ₀, hℓ₀ρ⟩ := exists_lift_pairing hρW hPρ hρ hιρ hsρ hf
  have hι₀ (a : Dual ℝ (LinearMap.ker B)) (w : W) : ω (ι w) (ℓ₀ a) = a (P w) := by
    simpa using hℓ₀ a w 0
  have hs₀ (a : Dual ℝ (LinearMap.ker B)) (v : V) : ω (s v) (ℓ₀ a) = 0 := by
    simpa using hℓ₀ a 0 v
  let κ : Dual ℝ (LinearMap.ker B) →ₗ[ℝ] LinearMap.ker B :=
    (evalEquiv ℝ (LinearMap.ker B)).symm.toLinearMap ∘ₗ
      ((-(1 / 2 : ℝ)) • ω.toBilinForm.compl₁₂ ℓ₀ ℓ₀)
  have hκ (a a' : Dual ℝ (LinearMap.ker B)) : a' (κ a) = -(1 / 2) * ω (ℓ₀ a) (ℓ₀ a') := by
    simp [κ]
  have hκρ (h : H) (a : Dual ℝ (LinearMap.ker B)) :
      (κ (B.kerDualRepresentation ρW hρW h a) : W) = ρW h (κ a) := by
    rw [← coe_kerRepresentation_apply hρW]
    congr 1
    refine (evalEquiv ℝ (LinearMap.ker B)).injective (LinearMap.ext fun a' ↦ ?_)
    have h₁ : a' (B.kerRepresentation ρW hρW h (κ a)) =
        B.kerDualRepresentation ρW hρW h⁻¹ a' (κ a) := by
      rw [kerDualRepresentation_apply_apply, inv_inv]
    simp only [evalEquiv_apply, Dual.eval_apply, h₁, hκ, hℓ₀ρ]
    rw [← isSymplectomorphism_toBilinForm_apply (hρ h) (ℓ₀ a)]
    simp
  refine ⟨ℓ₀ + ι ∘ₗ (LinearMap.ker B).subtype ∘ₗ κ, fun a w ↦ ?_, fun a v ↦ ?_,
    fun a a' ↦ ?_, fun h a ↦ ?_⟩
  · simp [hι₀, hω, hB.isRefl.apply_eq_zero_of_mem_ker w (κ a).2]
  · simp [hs₀, ← ω.neg_eq (ι _) (s v), hsι]
  · -- The cross terms `ω (ℓ₀ a) (ι κ a')` and `ω (ι κ a) (ℓ₀ a')` cancel `ω (ℓ₀ a) (ℓ₀ a')`.
    have h₁ := hι₀ a' (κ a)
    have h₂ := hι₀ a (κ a')
    rw [hP, hκ] at h₁ h₂
    have h₃ : ω (ℓ₀ a) (ι (κ a')) = -ω (ι (κ a')) (ℓ₀ a) := (ω.neg_eq _ _).symm
    have h₄ : ω (ℓ₀ a') (ℓ₀ a) = -ω (ℓ₀ a) (ℓ₀ a') := (ω.neg_eq _ _).symm
    simp only [LinearMap.add_apply, LinearMap.comp_apply, Submodule.subtype_apply, map_add,
      hω, LinearMap.mem_ker.1 (κ a).2, LinearMap.zero_apply, h₁, h₃, h₂, h₄]
    ring
  · simp [hℓ₀ρ, hκρ, hιρ]

omit [FiniteDimensional ℝ E] [Representation.IsSemisimpleRepresentation
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ)] in
/-- `(w, v) ↦ ι w + s v` is injective when `ι` is injective and `s` is a symplectic map, into
`(ι W)^ω`, out of a symplectic vector space `(V, ω_V)`. -/
private theorem injective_coprod {ωV : SymplecticForm V} (hι : Function.Injective ι)
    (hsι : ∀ w v, ω (ι w) (s v) = 0) (hs : ∀ v v', ω (s v) (s v') = ωV v v') :
    Function.Injective (ι.coprod s) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  rintro ⟨w, v⟩ hwv
  rw [LinearMap.mem_ker, LinearMap.coprod_apply] at hwv
  -- Pairing `ι w + s v = 0` with `s v'` shows that `v` pairs to zero with every `v'`.
  have hv : v = 0 := ωV.nondegenerate.2 v fun v' ↦ by
    have h₀ : ω.toBilinForm (s v') (ι w + s v) = 0 := by rw [hwv, map_zero]
    have h₁ := (ω.neg_eq (ι w) (s v')).symm
    beta_reduce at h₁ hsι hs
    rw [map_add, h₁, hsι, neg_zero, zero_add, hs] at h₀
    exact h₀
  subst hv
  rw [map_zero, add_zero] at hwv
  exact Prod.ext (hι (hwv.trans (map_zero ι).symm)) rfl

omit [Representation.IsSemisimpleRepresentation
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ)] in
/-- If `ℓ : K* → E` and `s : V → E` satisfy the pairing relations of the model, and the dimensions
match, then `((w, a), v) ↦ ι w + ℓ a + s v` is a linear symplectomorphism from the coisotropic
model on `W × K*` plus `(V, ω_V)` onto `E`. -/
private theorem exists_isSymplectomorphism_of_lift (hB : B.IsAlt)
    (hP : ∀ k : LinearMap.ker B, P k = k) {ωV : SymplecticForm V} [FiniteDimensional ℝ V]
    (hι : Function.Injective ι) (hω : ∀ w w', ω (ι w) (ι w') = B w w')
    (hsι : ∀ w v, ω (ι w) (s v) = 0) (hs : ∀ v v', ω (s v) (s v') = ωV v v')
    {ℓ : Dual ℝ (LinearMap.ker B) →ₗ[ℝ] E} (hℓι : ∀ a w, ω (ι w) (ℓ a) = a (P w))
    (hℓs : ∀ a v, ω (s v) (ℓ a) = 0) (hℓℓ : ∀ a a', ω (ℓ a) (ℓ a') = 0)
    (hdim : finrank ℝ W + finrank ℝ (LinearMap.ker B) + finrank ℝ V = finrank ℝ E) :
    ∃ e : ((W × Dual ℝ (LinearMap.ker B)) × V) ≃ₗ[ℝ] E,
      IsSymplectomorphism ((hB.coisotropicModel P hP).prod ωV) ω e ∧
        ∀ w a v, e ((w, a), v) = ι w + ℓ a + s v := by
  have : FiniteDimensional ℝ W := .of_injective ι hι
  let f := (ι.coprod ℓ).coprod s
  have hfω (x y) : ω.toBilinForm (f x) (f y) =
      ((hB.coisotropicModel P hP).prod ωV).toBilinForm x y := by
    obtain ⟨⟨w, a⟩, v⟩ := x
    obtain ⟨⟨w', a'⟩, v'⟩ := y
    have h₁ := (ω.neg_eq (ι w') (ℓ a)).symm
    have h₂ := (ω.neg_eq (ι w') (s v)).symm
    have h₃ := (ω.neg_eq (s v') (ℓ a)).symm
    beta_reduce at h₁ h₂ h₃ hω hsι hs hℓι hℓs hℓℓ
    simp only [f, LinearMap.coprod_apply, map_add, LinearMap.add_apply, h₁, h₂, h₃, hω, hsι, hs,
      hℓι, hℓs, hℓℓ]
    simp only [neg_zero, add_zero, zero_add, SymplecticForm.prod_apply, coisotropicModel_apply,
      add_left_inj]
    ring
  -- An isometry out of a nondegenerate form is injective, and the dimensions agree.
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    refine ((hB.coisotropicModel P hP).prod ωV).nondegenerate.1 x fun y ↦ ?_
    rw [← hfω, LinearMap.mem_ker.1 hx, map_zero, LinearMap.zero_apply]
  have hdim' : finrank ℝ ((W × Dual ℝ (LinearMap.ker B)) × V) = finrank ℝ E := by
    rw [Module.finrank_prod, Module.finrank_prod, Subspace.dual_finrank_eq, hdim]
  let e := f.linearEquivOfInjective hinj hdim'
  have he (x) : e x = f x := LinearMap.linearEquivOfInjective_apply hinj hdim' x
  exact ⟨e, isSymplectomorphism_iff.2 fun x y ↦ by rw [he, he]; exact hfω x y,
    fun w a v ↦ he _⟩

omit [Representation.IsSemisimpleRepresentation
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ)] in
/-- **The equivariant presymplectic Witt extension.** Let `H` act on a finite-dimensional
symplectic vector space `(E, ω)` by a semisimple representation `ρ` by symplectomorphisms, and on
`W` by `ρ_W`. Let `ι : W → E` be an injective equivariant linear map pulling `ω` back to the
alternating form `B`, with kernel `K`, and let `P : W → K` be an equivariant projection. Then `ι`
extends to an equivariant linear symplectomorphism

`(W × K*) × V ≃ E`, `((w, 0), 0) ↦ ι w`,

from the direct sum of the coisotropic model on `W × K*` and the reduced space
`V = (ι W)^ω ⧸ (ι W ∩ (ι W)^ω)`, which maps each `((0, 0), v)` to a vector of `(ι W)^ω` with
class `v`, so that it identifies `V` with an invariant complement of the radical. The group acts
on the model through `ρ_W` on `W`, the contragredient action on `K*` and the induced action on
`V`. -/
theorem exists_equivariant_isSymplectomorphism_coisotropicModel_prod (hB : B.IsAlt)
    (hP : ∀ k : LinearMap.ker B, P k = k) (hρW : ∀ h, B.IsOrthogonal (ρW h))
    (hPρ : ∀ h w, P (ρW h w) = B.kerRepresentation ρW hρW h (P w)) (ω : SymplecticForm E)
    (hρ : ∀ h, IsSymplectomorphism ω ω (ρ h))
    (hss : Representation.IsSemisimpleRepresentation
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ))
    (hι : Function.Injective ι) (hω : ∀ w w', ω (ι w) (ι w') = B w w')
    (hιρ : ∀ h w, ι (ρW h w) = ρ h (ι w))
    (hU : ∀ h, ∀ u ∈ ω.orthogonal (LinearMap.range ι), ρ h u ∈ ω.orthogonal (LinearMap.range ι)) :
    ∃ e : ((W × Dual ℝ (LinearMap.ker B)) × ω.ReducedSpace (ω.orthogonal (LinearMap.range ι)))
        ≃ₗ[ℝ] E,
      IsSymplectomorphism ((hB.coisotropicModel P hP).prod (ω.reduction _)) ω e ∧
        (∀ w, e ((w, 0), 0) = ι w) ∧
        (∀ v, ∃ hv : e ((0, 0), v) ∈ ω.orthogonal (LinearMap.range ι),
          Submodule.Quotient.mk ⟨_, hv⟩ = v) ∧
        ∀ h x v, e ((ρW h).prodCongr (B.kerDualRepresentation ρW hρW h) x,
          ω.reducedSpaceRepresentation ρ hρ _ hU h v) = ρ h (e (x, v)) := by
  have : FiniteDimensional ℝ W := .of_injective ι hι
  set U := ω.orthogonal (LinearMap.range ι)
  -- The equivariant section `s` of `U → V`, and the isotropic lift `ℓ` of `K*`.
  obtain ⟨s₀, hs₀, hs₀ρ⟩ := TauCeti.SymplecticForm.exists_equivariant_section_reducedSpace hρ hU
  have hsι (w : W) (v : ω.ReducedSpace U) : ω.toBilinForm (ι w) (s₀ v) = 0 :=
    mem_orthogonal_iff.1 (s₀ v).2 _ ⟨w, rfl⟩
  have hs (v v' : ω.ReducedSpace U) :
      ω.toBilinForm (s₀ v) (s₀ v') = (ω.reduction U).toBilinForm v v' := by
    conv_rhs => rw [← hs₀ v, ← hs₀ v']
    exact (reduction_mk ω U _ _).symm
  obtain ⟨ℓ, hℓι, hℓs, hℓℓ, hℓρ⟩ := exists_isotropic_lift hB hP hρW hPρ hρ hι hω hιρ
    (s := U.subtype ∘ₗ s₀) (σ := ω.reducedSpaceRepresentation ρ hρ U hU) hsι hs₀ρ
    (injective_coprod hι hsι hs)
  -- `dim K = dim (ι W ∩ (ι W)^ω)`, so the model has the dimension of `E`.
  have hdim : finrank ℝ W + finrank ℝ (LinearMap.ker B) + finrank ℝ (ω.ReducedSpace U) =
      finrank ℝ E := by
    have h₁ : finrank ℝ (ω.ReducedSpace U) + finrank ℝ (LinearMap.range ι) +
        finrank ℝ ↥(LinearMap.range ι ⊓ U) = finrank ℝ E :=
      ω.finrank_reducedSpace_orthogonal_add _
    have h₂ : LinearMap.range ι ⊓ U = (LinearMap.ker B).map ι := by
      rw [ker_eq_comap_orthogonal_range ω hω, Submodule.map_comap_eq]
    rw [h₂, ← (Submodule.equivMapOfInjective ι hι _).finrank_eq,
      LinearMap.finrank_range_of_inj hι] at h₁
    omega
  obtain ⟨e, he, hef⟩ := exists_isSymplectomorphism_of_lift hB hP hι hω hsι hs hℓι hℓs hℓℓ hdim
  have he₀ (v : ω.ReducedSpace U) : e ((0, 0), v) = s₀ v := by simp [hef]
  refine ⟨e, he, fun w ↦ by simp [hef], fun v ↦ ⟨by rw [he₀]; exact (s₀ v).2, ?_⟩,
    fun h ⟨w, a⟩ v ↦ ?_⟩
  · conv_rhs => rw [← hs₀ v]
    exact congrArg Submodule.Quotient.mk (Subtype.ext (he₀ v))
  simp only [LinearEquiv.prodCongr_apply, hef, LinearMap.comp_apply, Submodule.subtype_apply,
    map_add, hιρ, hℓρ]
  rw [hs₀ρ h v]

end LinearMap.BilinForm.IsAlt
