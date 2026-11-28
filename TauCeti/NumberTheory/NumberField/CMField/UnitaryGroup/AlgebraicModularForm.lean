/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Topology.Algebra.Group.Matrix
public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.AdelicFrame
public import TauCeti.RepresentationTheory.Coinduced
public import TauCeti.RepresentationTheory.Smooth.Basic

/-!
# Algebraic modular forms on a hermitian space with an adelic frame

Let `E` be a CM field, `V = (J, x)` a hermitian space with an adelic frame of signs `s`
(`TauCeti.FramedHermitianSpace`), `G_f` the finite adelic unitary group, `G_∞(s)` the archimedean
one and `G(s) = G_∞(s) × G_f`. Let `ρ` be a representation of `G_∞(s)` on a module `W` over a
commutative semiring `A`. The group `U(J)(E⁺)` of rational points acts on `W` through
`γ ↦ ρ((x⁻¹ γ x)_∞)`, the **coefficient representation**
(`TauCeti.FramedHermitianSpace.coefficientRep`).

An **algebraic modular form** of coefficients `ρ` on `V` is a function `φ : G_f → W` with
`φ(γ_f g) = ρ(γ_∞) φ(g)` for every rational point `γ ∈ Γ_V`, with components `γ_∞` and `γ_f`, and
every `g ∈ G_f`, whose stabilizer under right translation is open. The functions satisfying the
first condition form Mathlib's representation `Representation.coind` of `G_f` coinduced from the
coefficient representation along `γ ↦ (x⁻¹ γ x)_f`, on which `G_f` acts by right translation, and
the algebraic modular forms are its smooth vectors
(`TauCeti.FramedHermitianSpace.algebraicModularForms`). For a subgroup `K` of `G_f` and a
character `χ` of `K`, the forms of level `(K, χ)` are those with `φ(g k) = χ(k) φ(g)`.

For a definite space (`s = (1, …, 1)`), `G_∞(s) = U(n)^Φ` is compact, and with `ρ` the algebraic
representation of a weight `(κ, e)` read through the conjugate embeddings, these are the
algebraic modular forms of Gross: at a fixed level `K`, the functions of Gross's rational model
`F(γ g) = ρ(γ) F(g)`, `F(g k) = F(g)`, for the unitary group of `(E^n, h_J)` over `E⁺`. The
definitions here make sense for every sign vector and every coefficient representation.

For a linear form `L` on `W`, the function `φ_L(z, g) = L(ρ(z)⁻¹ φ(g))` on `G(s)`
(`Representation.adelicFunction`) is left invariant under `Γ_V`, right invariant
under the stabilizer of `φ`, and continuous when `φ` is a form and the matrix coefficients
`z ↦ L(ρ(z) w)` are continuous. It recovers `L(φ(g))` through `φ_L(1, g) = L(φ(g))`, so the
`φ_L` for all `L` determine `φ` when `W` is projective. This is how algebraic modular forms are
compared with automorphic functions on `G(s)`.

## Main definitions

* `TauCeti.FramedHermitianSpace.coefficientRep V ρ`: the representation `γ ↦ ρ((x⁻¹ γ x)_∞)` of
  `U(J)(E⁺)`.
* `TauCeti.FramedHermitianSpace.algebraicModularForms V ρ`: the algebraic modular forms, the
  subrepresentation of smooth vectors of the coinduced representation of `G_f`.
* `TauCeti.FramedHermitianSpace.algebraicModularFormsOfLevel V ρ K χ`: the forms of level
  `(K, χ)`.
* `Representation.adelicFunction ρ L`: the linear map `φ ↦ φ_L`.

## Main results

* `TauCeti.FramedHermitianSpace.mem_coindV_finiteRationalEmbedding_iff`: the coinduced functions
  are the `φ` with `φ(γ_f g) = ρ(γ_∞) φ(g)` for `γ ∈ Γ_V`.
* `TauCeti.FramedHermitianSpace.mem_algebraicModularForms_iff`: a coinduced function is a form
  exactly when it is invariant under right translation by an open subgroup of `G_f`, and
  `TauCeti.FramedHermitianSpace.mem_algebraicModularForms_iff_exists_isUnitaryLevel`: exactly when
  it has some level `K ⊆ K₀` with trivial character.
* `TauCeti.FramedHermitianSpace.algebraicModularFormsOfLevel_one_of_isOpen`: for an open `K`, the
  forms of level `(K, 1)` are all the `K`-invariant coinduced functions.
* `Representation.adelicFunction_rationalPoint_mul`, `Representation.adelicFunction_mul_ofFinite`,
  `Representation.adelicFunction_mul_ofInfinite`, `Representation.continuous_adelicFunction`,
  `Representation.forall_adelicFunction_eq_iff`: the properties of `φ_L`.

## References

* B. H. Gross, *Algebraic modular forms*, Israel J. Math. 113 (1999), 61–93, §§2, 4.

## Attribution

The objects defined here, the coefficient representation, the algebraic modular forms with their
action of `G_f`, and the function `φ_L`, follow `New.Space.weightRep`, `New.AlgForm`,
`New.algFormRep` and `New.ofAlgForm` in `src/Lib/Adelic/AutomorphicForms/SmoothAlgebraicForms.lean`
of grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC); the
formalization here, through coinduced representations and their smooth vectors, is independent of
that code.
-/

public section
noncomputable section

open Matrix NumberField Representation Topology

namespace TauCeti

namespace FramedHermitianSpace

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] {ι : Type*} [Fintype ι]
  [DecidableEq ι] {s : ι → ℤˣ} (V : FramedHermitianSpace E s)
  {A W : Type*} [CommSemiring A] [AddCommMonoid W] [Module A W]
  (ρ : Representation A (infiniteAdelicUnitaryGroup E s) W)

/-! ### The coefficient representation -/

/-- The **coefficient representation** of a space `V = (J, x)` with an adelic frame and a
representation `ρ` of `G_∞(s)`: the representation `γ ↦ ρ((x⁻¹ γ x)_∞)` of the rational points
`U(J)(E⁺)`, through the archimedean rational embedding. -/
def coefficientRep : Representation A (unitaryGroupOf V.gram) W :=
  ρ.comp V.infiniteRationalEmbedding

/-- The coefficient representation is `γ ↦ ρ((x⁻¹ γ x)_∞)`. -/
@[simp]
theorem coefficientRep_apply (γ : unitaryGroupOf V.gram) :
    V.coefficientRep ρ γ = ρ (V.infiniteRationalEmbedding γ) :=
  (rfl)

/-- **The coinduced functions.** A function `φ : G_f → W` lies in the representation coinduced
from the coefficient representation along `γ ↦ (x⁻¹ γ x)_f` exactly when
`φ(γ_f g) = ρ(γ_∞) φ(g)` for every rational point `γ ∈ Γ_V` and every `g ∈ G_f`. -/
theorem mem_coindV_finiteRationalEmbedding_iff {φ : finiteAdelicUnitaryGroup E ι → W} :
    φ ∈ coindV V.finiteRationalEmbedding (V.coefficientRep ρ) ↔
      ∀ γ ∈ V.rationalPoints, ∀ g, φ (adelicUnitaryGroup.finitePart E s γ * g) =
        ρ (adelicUnitaryGroup.infinitePart E s γ) (φ g) := by
  simp only [mem_coindV, coefficientRep_apply, rationalPoints_def, MonoidHom.mem_range,
    forall_exists_index, forall_apply_eq_imp_iff, finitePart_rationalEmbedding,
    infinitePart_rationalEmbedding]

/-! ### Algebraic modular forms -/

/-- The **algebraic modular forms** of coefficients `ρ` on a space `V` with an adelic frame: the
functions `φ : G_f → W` with `φ(γ_f g) = ρ(γ_∞) φ(g)` for every rational point `γ ∈ Γ_V`
(`mem_coindV_finiteRationalEmbedding_iff`), whose stabilizer under right translation is open
(`mem_algebraicModularForms_iff`). They are the smooth vectors of the representation of `G_f`
coinduced from the coefficient representation along `γ ↦ (x⁻¹ γ x)_f`, a subrepresentation for the
action of `G_f` by right translation. -/
def algebraicModularForms :
    Subrepresentation (coind V.finiteRationalEmbedding (V.coefficientRep ρ)) :=
  (coind V.finiteRationalEmbedding (V.coefficientRep ρ)).smoothVectors

/-- A coinduced function is an algebraic modular form exactly when its stabilizer under right
translation is open. -/
theorem mem_algebraicModularForms_iff_isOpen
    {φ : coindV V.finiteRationalEmbedding (V.coefficientRep ρ)} :
    φ ∈ V.algebraicModularForms ρ ↔
      IsOpen ((coind V.finiteRationalEmbedding (V.coefficientRep ρ)).stabilizer φ :
        Set (finiteAdelicUnitaryGroup E ι)) := by
  rw [algebraicModularForms, mem_smoothVectors_iff]

/-- A coinduced function is an algebraic modular form exactly when it is invariant under right
translation by some open subgroup of `G_f`. -/
theorem mem_algebraicModularForms_iff
    {φ : coindV V.finiteRationalEmbedding (V.coefficientRep ρ)} :
    φ ∈ V.algebraicModularForms ρ ↔
      ∃ U : OpenSubgroup (finiteAdelicUnitaryGroup E ι), ∀ u ∈ U, ∀ g, φ.val (g * u) = φ.val g := by
  rw [algebraicModularForms, mem_smoothVectors_iff_exists_openSubgroup]
  simp only [stabilizer_coind_eq]
  exact exists_congr fun U ↦ ⟨fun h u hu ↦ mem_rightTranslationStabilizer.1 (h hu),
    fun h u hu ↦ mem_rightTranslationStabilizer.2 (h u hu)⟩

/-- **Algebraic modular forms are locally constant** functions on `G_f`. -/
theorem isLocallyConstant_val_of_mem_algebraicModularForms
    {φ : coindV V.finiteRationalEmbedding (V.coefficientRep ρ)}
    (hφ : φ ∈ V.algebraicModularForms ρ) : IsLocallyConstant φ.val :=
  isLocallyConstant_of_isOpen_rightTranslationStabilizer <|
    stabilizer_coind_eq φ ▸ (V.mem_algebraicModularForms_iff_isOpen ρ).1 hφ

-- Not `@[simp]`: simp unfolds the action through `Subrepresentation.coe_toRepresentation_apply`
-- and `Representation.coind_apply`, so the left-hand side is not in simp-normal form (`simpNF`).
/-- The action of `g ∈ G_f` on algebraic modular forms is right translation by `g`. -/
theorem algebraicModularForms_toRepresentation_apply_val_apply
    (g h : finiteAdelicUnitaryGroup E ι) (φ : V.algebraicModularForms ρ) :
    ((V.algebraicModularForms ρ).toRepresentation g φ :
      coindV V.finiteRationalEmbedding (V.coefficientRep ρ)).val h =
        (φ : coindV V.finiteRationalEmbedding (V.coefficientRep ρ)).val (h * g) := by
  simp only [Subrepresentation.coe_toRepresentation_apply, coind_apply_coe_apply]

/-! ### Forms of a level -/

/-- The **algebraic modular forms of level `(K, χ)`**, for a subgroup `K` of `G_f` and a character
`χ` of `K`: the forms with `φ(g k) = χ(k) φ(g)` for `k ∈ K` and `g ∈ G_f`
(`mem_algebraicModularFormsOfLevel_iff`), the forms in the `χ`-weight space of the restriction to
`K` of the coinduced representation. -/
def algebraicModularFormsOfLevel (K : Subgroup (finiteAdelicUnitaryGroup E ι)) (χ : K →* A) :
    Submodule A (coindV V.finiteRationalEmbedding (V.coefficientRep ρ)) :=
  (V.algebraicModularForms ρ).toSubmodule ⊓
    weightSpace ((coind V.finiteRationalEmbedding (V.coefficientRep ρ)).comp K.subtype) χ

/-- A coinduced function is a form of level `(K, χ)` exactly when it is an algebraic modular form
with `φ(g k) = χ(k) φ(g)` for `k ∈ K` and `g ∈ G_f`. -/
theorem mem_algebraicModularFormsOfLevel_iff {K : Subgroup (finiteAdelicUnitaryGroup E ι)}
    {χ : K →* A} {φ : coindV V.finiteRationalEmbedding (V.coefficientRep ρ)} :
    φ ∈ V.algebraicModularFormsOfLevel ρ K χ ↔
      φ ∈ V.algebraicModularForms ρ ∧ ∀ (k : K) g, φ.val (g * k) = χ k • φ.val g := by
  simp only [algebraicModularFormsOfLevel, Submodule.mem_inf, Subrepresentation.mem_toSubmodule,
    mem_weightSpace_coind_comp_subtype_iff]

/-- **Forms of an open level.** For an open subgroup `K` of `G_f`, the forms of level `(K, 1)` are
all the coinduced functions invariant under right translation by `K`: these are automatically
smooth. -/
theorem algebraicModularFormsOfLevel_one_of_isOpen {K : Subgroup (finiteAdelicUnitaryGroup E ι)}
    (hK : IsOpen (K : Set (finiteAdelicUnitaryGroup E ι))) :
    V.algebraicModularFormsOfLevel ρ K 1 =
      weightSpace ((coind V.finiteRationalEmbedding (V.coefficientRep ρ)).comp K.subtype) 1 := by
  refine inf_eq_right.2 fun φ hφ ↦ (V.mem_algebraicModularForms_iff ρ).2 ⟨⟨K, hK⟩, fun u hu g ↦ ?_⟩
  simpa only [MonoidHom.one_apply, one_smul] using
    mem_weightSpace_coind_comp_subtype_iff.1 hφ ⟨u, hu⟩ g

/-- Forms of level `(K, χ)` are forms of level `(K', χ|_{K'})` for every `K' ≤ K`. -/
theorem algebraicModularFormsOfLevel_mono {K K' : Subgroup (finiteAdelicUnitaryGroup E ι)}
    (hK : K' ≤ K) (χ : K →* A) :
    V.algebraicModularFormsOfLevel ρ K χ ≤
      V.algebraicModularFormsOfLevel ρ K' (χ.comp (Subgroup.inclusion hK)) := fun φ hφ ↦ by
  rw [mem_algebraicModularFormsOfLevel_iff] at hφ ⊢
  exact ⟨hφ.1, fun k g ↦ hφ.2 (Subgroup.inclusion hK k) g⟩

/-- **Every algebraic modular form has a level.** A coinduced function is an algebraic modular form
exactly when it is a form of level `(K, 1)` for some level `K`, an open subgroup of
`K₀ = G_f ∩ GL_n(Ô)`. -/
theorem mem_algebraicModularForms_iff_exists_isUnitaryLevel
    {φ : coindV V.finiteRationalEmbedding (V.coefficientRep ρ)} :
    φ ∈ V.algebraicModularForms ρ ↔
      ∃ K, IsUnitaryLevel K ∧ φ ∈ V.algebraicModularFormsOfLevel ρ K 1 := by
  refine ⟨fun hφ ↦ ?_, fun ⟨K, _, hK⟩ ↦ ((V.mem_algebraicModularFormsOfLevel_iff ρ).1 hK).1⟩
  obtain ⟨U, hU⟩ := (V.mem_algebraicModularForms_iff ρ).1 hφ
  have hK : IsUnitaryLevel (U ⊓ integralAdelicUnitaryGroup E ι) :=
    ⟨inf_le_right, U.isOpen.inter (isOpen_integralAdelicUnitaryGroup E ι)⟩
  refine ⟨_, hK, (V.mem_algebraicModularFormsOfLevel_iff ρ).2 ⟨hφ, fun k g ↦ ?_⟩⟩
  simpa using hU k (Subgroup.mem_inf.1 k.property).1 g

end FramedHermitianSpace

end TauCeti

/-! ### The adelic function of a form -/

namespace Representation

open TauCeti

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] {ι : Type*} [Fintype ι]
  [DecidableEq ι] {s : ι → ℤˣ} {A W : Type*} [CommSemiring A] [AddCommMonoid W] [Module A W]
  (ρ : Representation A (infiniteAdelicUnitaryGroup E s) W)

/-- For a linear form `L` on `W`, the linear map `φ ↦ φ_L` from functions `φ : G_f → W` to functions
on `G(s)`, `φ_L(g) = L(ρ(g_∞)⁻¹ φ(g_f))`. For an algebraic modular form `φ`, `φ_L` is left invariant
under the rational points (`adelicFunction_rationalPoint_mul`) and right invariant under the
stabilizer of `φ` (`adelicFunction_mul_ofFinite`). -/
def adelicFunction (L : W →ₗ[A] A) :
    (finiteAdelicUnitaryGroup E ι → W) →ₗ[A] adelicUnitaryGroup E s → A where
  toFun φ g :=
    L (ρ (adelicUnitaryGroup.infinitePart E s g)⁻¹ (φ (adelicUnitaryGroup.finitePart E s g)))
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/-- `φ_L(g) = L(ρ(g_∞)⁻¹ φ(g_f))`. -/
@[simp]
theorem adelicFunction_apply (L : W →ₗ[A] A) (φ : finiteAdelicUnitaryGroup E ι → W)
    (g : adelicUnitaryGroup E s) :
    adelicFunction ρ L φ g =
      L (ρ (adelicUnitaryGroup.infinitePart E s g)⁻¹ (φ (adelicUnitaryGroup.finitePart E s g))) :=
  (rfl)

/-- On the finite adelic points, `φ_L(1, g) = L(φ(g))`. -/
theorem adelicFunction_ofFinite (L : W →ₗ[A] A) (φ : finiteAdelicUnitaryGroup E ι → W)
    (g : finiteAdelicUnitaryGroup E ι) :
    adelicFunction ρ L φ (adelicUnitaryGroup.ofFinite E s g) = L (φ g) := by
  simp

/-- **`φ_L` is invariant under the rational points**: `φ_L(γ g) = φ_L(g)` for `γ ∈ Γ_V`, when `φ`
satisfies `φ(γ_f g) = ρ(γ_∞) φ(g)`. -/
theorem adelicFunction_rationalPoint_mul (L : W →ₗ[A] A)
    {V : FramedHermitianSpace E s} {φ : finiteAdelicUnitaryGroup E ι → W}
    (hφ : φ ∈ coindV V.finiteRationalEmbedding (V.coefficientRep ρ))
    {γ : adelicUnitaryGroup E s} (hγ : γ ∈ V.rationalPoints) (g : adelicUnitaryGroup E s) :
    adelicFunction ρ L φ (γ * g) = adelicFunction ρ L φ g := by
  simp [(V.mem_coindV_finiteRationalEmbedding_iff ρ).1 hφ γ hγ, map_mul, _root_.mul_inv_rev]

/-- Right translation by `(1, u)` on `φ_L` is right translation by `u` on `φ`:
`φ_L(g (1, u)) = ψ_L(g)` for `ψ(h) = φ(h u)`. -/
theorem adelicFunction_mul_ofFinite (L : W →ₗ[A] A) (φ : finiteAdelicUnitaryGroup E ι → W)
    (g : adelicUnitaryGroup E s) (u : finiteAdelicUnitaryGroup E ι) :
    adelicFunction ρ L φ (g * adelicUnitaryGroup.ofFinite E s u) =
      adelicFunction ρ L (fun h ↦ φ (h * u)) g := by
  simp

/-- Right translation by `(z, 1)` on `φ_L` replaces `L` by `L ∘ ρ(z)⁻¹`:
`φ_L(g (z, 1)) = φ_{L ∘ ρ(z)⁻¹}(g)`. -/
theorem adelicFunction_mul_ofInfinite (L : W →ₗ[A] A) (φ : finiteAdelicUnitaryGroup E ι → W)
    (g : adelicUnitaryGroup E s) (z : infiniteAdelicUnitaryGroup E s) :
    adelicFunction ρ L φ (g * adelicUnitaryGroup.ofInfinite E s z) =
      adelicFunction ρ (L ∘ₗ ρ z⁻¹) φ g := by
  simp [_root_.mul_inv_rev, map_mul]

/-- **`φ_L` is continuous** when `φ` is locally constant (for instance an algebraic modular form,
`TauCeti.FramedHermitianSpace.isLocallyConstant_val_of_mem_algebraicModularForms`) and the matrix
coefficients `z ↦ L(ρ(z) w)` of `ρ` are continuous on `G_∞(s)`. -/
theorem continuous_adelicFunction [TopologicalSpace A] (L : W →ₗ[A] A)
    (hL : ∀ w, Continuous fun z ↦ L (ρ z w)) {φ : finiteAdelicUnitaryGroup E ι → W}
    (hφ : IsLocallyConstant φ) : Continuous (adelicFunction ρ L φ) := by
  refine continuous_iff_continuousAt.2 fun g ↦ ?_
  -- near `g`, the finite component stays where `φ` takes the value `φ(g_f)`
  have hev : adelicFunction ρ L φ =ᶠ[𝓝 g] fun h ↦
      L (ρ (adelicUnitaryGroup.infinitePart E s h)⁻¹ (φ (adelicUnitaryGroup.finitePart E s g))) :=
    ((adelicUnitaryGroup.continuous_finitePart s).continuousAt.eventually
      (hφ.eventually_eq _)).mono fun h hh ↦ by simp [hh]
  refine ContinuousAt.congr ?_ hev.symm
  exact ((hL _).comp ((adelicUnitaryGroup.continuous_infinitePart s).inv)).continuousAt

/-- **The `φ_L` determine `φ`**: for a projective module `W` over a commutative ring, two functions
`φ, ψ : G_f → W` are equal exactly when `φ_L = ψ_L` for every linear form `L`, as
`φ_L(1, g) = L(φ(g))` and linear forms separate points of a projective module. -/
theorem forall_adelicFunction_eq_iff {A W : Type*} [CommRing A] [AddCommGroup W] [Module A W]
    [Module.Projective A W] (ρ : Representation A (infiniteAdelicUnitaryGroup E s) W)
    {φ ψ : finiteAdelicUnitaryGroup E ι → W} :
    (∀ L : W →ₗ[A] A, adelicFunction ρ L φ = adelicFunction ρ L ψ) ↔ φ = ψ := by
  refine ⟨fun h ↦ funext fun g ↦ sub_eq_zero.1 ?_, fun h _ ↦ h ▸ rfl⟩
  refine (Module.forall_dual_apply_eq_zero_iff A _).1 fun L ↦ ?_
  have := congrFun (h L) (adelicUnitaryGroup.ofFinite E s g)
  rw [adelicFunction_ofFinite, adelicFunction_ofFinite] at this
  rw [map_sub, this, sub_self]

end Representation
