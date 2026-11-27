/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.RepresentationTheory.Basic
public import TauCeti.GroupTheory.SpecificGroups.Heisenberg.Bilinear
public import TauCeti.LinearAlgebra.BilinearForm.Polarization
public import TauCeti.Topology.LocallyConstant.CompactSupport

/-!
# The Schrödinger representation of a polarized Heisenberg group

Let `B : X × Y → C` be a pairing and `W = X × Y` the polarization it defines, with symplectic
form `ω((x, y), (x', y')) = B x y' - B x' y`. Fix an additive character `ψ` of `C`. The Heisenberg
group of `W`, in the half-form convention `(t, w)(s, v) = (t + s + ½ω(w, v), w + v)`, acts on
functions `φ : X → V` by translation and modulation:

`ρψ(t, (x, y)) φ (u) = ψ (t + B u y + ½ B x y) φ (u + x)`.

This is the **Schrödinger representation** (`LinearMap.schroedinger`); its centre acts by the
character `ψ` (`LinearMap.schroedinger_inl`). It is the model with which Stone–von Neumann compares
every irreducible representation with central character `ψ`, and on which symplectic
automorphisms act up to scalars, giving the Weil representation of the metaplectic group.

The group law is cleanest in the polarized coordinates of the Heisenberg group, the extension
of the polarized form `B'((x, y), (x', y')) = B x y'` (`LinearMap.polarizedForm`), with law
`(t, w)(s, v) = (t + s + B x y', w + v)`. There the action is
`(t, (x, y)) φ (u) = ψ (t + B u y) φ (u + x)` (`LinearMap.polarizedSchroedinger`), which needs no
division by `2`. The half-form representation is its composite with the isomorphism
`(t, w) ↦ (t + ½B'(w, w), w)` of `LinearMap.BilinMap.polarizationEquiv`.

Two properties fix the analytic models. When `ψ` is locally constant, as is every continuous
unitary character of a nonarchimedean local field, the operators preserve the
locally constant compactly supported functions, the Schwartz–Bruhat space `S(X)`
(`LinearMap.schroedingerCompactlySupported`). When `ψ` is unitary, each operator acts on norms by
translation, so it preserves `∫ ‖φ‖ ^ 2` for a translation-invariant measure on `X`
(`LinearMap.integral_norm_sq_schroedinger_apply`); this is what makes the operators unitary on
`L²` once they descend to it. The archimedean model on the Schwartz space is
`TauCeti.RepresentationTheory.Heisenberg.Schroedinger.Schwartz`.

## Main definitions

* `LinearMap.polarizedSchroedinger`: the Schrödinger representation in polarized coordinates.
* `LinearMap.schroedinger`: the Schrödinger representation of the half-form Heisenberg group.
* `LinearMap.schroedingerCompactlySupported`: its restriction to `S(X)`.

## Main results

* `LinearMap.polarizedSchroedinger_apply`, `LinearMap.schroedinger_apply`: the translation and
  modulation formulas.
* `LinearMap.schroedinger_eq_polarizedSchroedinger`: the half-form representation is the
  polarized one transported along `LinearMap.BilinMap.polarizationEquiv`.
* `LinearMap.polarizedSchroedinger_inl`, `LinearMap.schroedinger_inl`: the centre acts by `ψ`.
* `LinearMap.isLocallyConstant_schroedinger_apply`,
  `LinearMap.hasCompactSupport_schroedinger_apply`: the operators preserve local
  constancy (for `ψ` locally constant) and compact support.
* `LinearMap.norm_schroedinger_apply`, `LinearMap.integral_norm_sq_schroedinger_apply`: for a
  unitary character the operators act on norms by translation, and preserve `∫ ‖φ‖ ^ 2` for a
  translation-invariant measure.

## References

* S. Kudla, *Notes on the local theta correspondence* (1996), I.2, Lemma 2.2.
* A. Weil, *Sur certains groupes d'opérateurs unitaires*, Acta Math. 111 (1964), I.§4.
-/

public section

noncomputable section

open Multiplicative TauCeti MeasureTheory

attribute [local instance] trivialMulDistribMulAction

namespace LinearMap

variable {R X Y C k : Type*} [CommSemiring R] [AddCommGroup X] [Module R X]
  [AddCommGroup Y] [Module R Y] [AddCommGroup C] [Module R C] [CommSemiring k]

section Polarized

variable (B : X →ₗ[R] Y →ₗ[R] C) (ψ : AddChar C k) (V : Type*) [AddCommMonoid V] [Module k V]

/-- **The Schrödinger representation in polarized coordinates.** The Heisenberg group of the
polarized form `B'((x, y), (x', y')) = B x y'`, with law `(t, w)(s, v) = (t + s + B x y', w + v)`,
acts on functions `φ : X → V` by `(t, (x, y)) φ (u) = ψ (t + B u y) φ (u + x)`. -/
def polarizedSchroedinger :
    Representation k B.polarizedForm.bilinearFactorSet.Extension (X → V) where
  toFun p :=
    { toFun φ u := ψ (p.left.toAdd + B u p.right.toAdd.2) • φ (u + p.right.toAdd.1)
      map_add' φ φ' := funext fun u ↦ smul_add _ _ _
      map_smul' c φ := funext fun u ↦ smul_comm _ c _ }
  map_one' := LinearMap.ext fun φ ↦ funext fun u ↦ by simp
  map_mul' p q := LinearMap.ext fun φ ↦ funext fun u ↦ by
    simp [smul_smul, ← AddChar.map_add_eq_mul, add_assoc, add_left_comm, add_comm]

/-- The polarized Schrödinger operator of `(t, (x, y))` translates by `x` and modulates by
`u ↦ ψ (t + B u y)`. -/
@[simp]
theorem polarizedSchroedinger_apply (p : B.polarizedForm.bilinearFactorSet.Extension)
    (φ : X → V) (u : X) :
    B.polarizedSchroedinger ψ V p φ u =
      ψ (p.left.toAdd + B u p.right.toAdd.2) • φ (u + p.right.toAdd.1) :=
  (rfl)

/-- The centre of the Heisenberg group acts on the Schrödinger representation by the
character `ψ`. -/
@[simp]
theorem polarizedSchroedinger_inl (t : C) :
    B.polarizedSchroedinger ψ V (FactorSet.inl _ (ofAdd t)) = ψ t • LinearMap.id :=
  LinearMap.ext fun φ ↦ funext fun u ↦ by simp

end Polarized

section HalfForm

variable [Invertible (2 : R)] (B : X →ₗ[R] Y →ₗ[R] C) (ψ : AddChar C k) (V : Type*)
  [AddCommMonoid V] [Module k V]

/-- **The Schrödinger representation.** The Heisenberg group of the symplectic form
`ω((x, y), (x', y')) = B x y' - B x' y` on `X × Y`, in the half-form convention
`(t, w)(s, v) = (t + s + ½ω(w, v), w + v)`, acts on functions `φ : X → V` by
`(t, (x, y)) φ (u) = ψ (t + B u y + ½ B x y) φ (u + x)` (`LinearMap.schroedinger_apply`). -/
def schroedinger :
    Representation k
      (⅟(2 : R) • (B.polarizedForm - B.polarizedForm.flip)).bilinearFactorSet.Extension
      (X → V) :=
  (B.polarizedSchroedinger ψ V).comp
    (B.polarizedForm.polarizationEquiv : _ ≃* _).toMonoidHom

/-- The half-form Schrödinger representation is the polarized one transported along the
isomorphism `(t, w) ↦ (t + ½B'(w, w), w)` of polarized coordinates. -/
theorem schroedinger_eq_polarizedSchroedinger
    (p : (⅟(2 : R) • (B.polarizedForm - B.polarizedForm.flip)).bilinearFactorSet.Extension) :
    B.schroedinger ψ V p = B.polarizedSchroedinger ψ V (B.polarizedForm.polarizationEquiv p) :=
  (rfl)

/-- The Schrödinger operator of `(t, (x, y))` translates by `x` and modulates by
`u ↦ ψ (t + B u y + ½ B x y)`. -/
@[simp]
theorem schroedinger_apply
    (p : (⅟(2 : R) • (B.polarizedForm - B.polarizedForm.flip)).bilinearFactorSet.Extension)
    (φ : X → V) (u : X) :
    B.schroedinger ψ V p φ u =
      ψ (p.left.toAdd + B u p.right.toAdd.2 + ⅟(2 : R) • B p.right.toAdd.1 p.right.toAdd.2) •
        φ (u + p.right.toAdd.1) := by
  rw [schroedinger_eq_polarizedSchroedinger, polarizedSchroedinger_apply,
    BilinMap.polarizationEquiv_apply]
  simp only [toAdd_mul, toAdd_ofAdd, polarizedForm_apply]
  congr 2
  abel

/-- The centre of the Heisenberg group acts on the Schrödinger representation by the
character `ψ`. -/
@[simp]
theorem schroedinger_inl (t : C) :
    B.schroedinger ψ V (FactorSet.inl _ (ofAdd t)) = ψ t • LinearMap.id :=
  LinearMap.ext fun φ ↦ funext fun u ↦ by simp

end HalfForm

/-! ### The Schwartz–Bruhat model -/

section CompactlySupported

variable [TopologicalSpace X] [ContinuousAdd X] {B : X →ₗ[R] Y →ₗ[R] C} {ψ : AddChar C k}
  {V : Type*} [AddCommMonoid V] [Module k V]

/-- The polarized Schrödinger operators preserve compact support. -/
theorem hasCompactSupport_polarizedSchroedinger_apply
    (p : B.polarizedForm.bilinearFactorSet.Extension) {φ : X → V} (hφ : HasCompactSupport φ) :
    HasCompactSupport (B.polarizedSchroedinger ψ V p φ) := by
  rw [funext (polarizedSchroedinger_apply B ψ V p φ)]
  exact (hφ.comp_homeomorph (Homeomorph.addRight _)).smul_left

/-- The Schrödinger operators preserve compact support. -/
theorem hasCompactSupport_schroedinger_apply [Invertible (2 : R)]
    (p : (⅟(2 : R) • (B.polarizedForm - B.polarizedForm.flip)).bilinearFactorSet.Extension)
    {φ : X → V} (hφ : HasCompactSupport φ) :
    HasCompactSupport (B.schroedinger ψ V p φ) := by
  rw [schroedinger_eq_polarizedSchroedinger]
  exact hasCompactSupport_polarizedSchroedinger_apply _ hφ

variable [TopologicalSpace C]

/-- If `ψ` is locally constant and each `B · y` is continuous, the polarized Schrödinger
operators preserve local constancy. -/
theorem isLocallyConstant_polarizedSchroedinger_apply (hψ : IsLocallyConstant ψ)
    (hB : ∀ y, Continuous fun u ↦ B u y) (p : B.polarizedForm.bilinearFactorSet.Extension)
    {φ : X → V} (hφ : IsLocallyConstant φ) :
    IsLocallyConstant (B.polarizedSchroedinger ψ V p φ) := by
  rw [funext (polarizedSchroedinger_apply B ψ V p φ)]
  have hmod : IsLocallyConstant fun u ↦ ψ (p.left.toAdd + B u p.right.toAdd.2) := by
    simp_rw [AddChar.map_add_eq_mul]
    exact (hψ.comp_continuous (hB _)).comp (ψ p.left.toAdd * ·)
  exact hmod.comp₂ (hφ.comp_continuous (continuous_id.add continuous_const)) (· • ·)

variable [Invertible (2 : R)]

/-- If `ψ` is locally constant and each `B · y` is continuous, the Schrödinger operators
preserve local constancy. -/
theorem isLocallyConstant_schroedinger_apply (hψ : IsLocallyConstant ψ)
    (hB : ∀ y, Continuous fun u ↦ B u y)
    (p : (⅟(2 : R) • (B.polarizedForm - B.polarizedForm.flip)).bilinearFactorSet.Extension)
    {φ : X → V} (hφ : IsLocallyConstant φ) :
    IsLocallyConstant (B.schroedinger ψ V p φ) := by
  rw [schroedinger_eq_polarizedSchroedinger]
  exact isLocallyConstant_polarizedSchroedinger_apply hψ hB _ hφ

/-- The Schrödinger operator of `p` on a locally constant compactly supported function. -/
private def schroedingerCompactlySupportedAux (hψ : IsLocallyConstant ψ)
    (hB : ∀ y, Continuous fun u ↦ B u y)
    (p : (⅟(2 : R) • (B.polarizedForm - B.polarizedForm.flip)).bilinearFactorSet.Extension)
    (f : LocallyConstant.compactlySupported k X V) : LocallyConstant.compactlySupported k X V :=
  ⟨⟨B.schroedinger ψ V p f.val,
      isLocallyConstant_schroedinger_apply hψ hB p f.val.isLocallyConstant⟩,
    LocallyConstant.mem_compactlySupported.2 <| hasCompactSupport_schroedinger_apply p
      (LocallyConstant.mem_compactlySupported.1 f.property)⟩

private theorem coe_schroedingerCompactlySupportedAux (hψ : IsLocallyConstant ψ)
    (hB : ∀ y, Continuous fun u ↦ B u y)
    (p : (⅟(2 : R) • (B.polarizedForm - B.polarizedForm.flip)).bilinearFactorSet.Extension)
    (f : LocallyConstant.compactlySupported k X V) :
    ⇑(schroedingerCompactlySupportedAux hψ hB p f : LocallyConstant X V) =
      B.schroedinger ψ V p f.val :=
  (rfl)

variable (B ψ V) in
/-- **The Schrödinger representation on the Schwartz–Bruhat space** `S(X)` of locally constant
compactly supported functions, for a locally constant character `ψ` (for instance a continuous
unitary character of a nonarchimedean local field, which is trivial on a neighbourhood of `0` by
`AddChar.setOf_eq_one_mem_nhds_zero`) and a pairing with continuous partial maps `B · y`. -/
def schroedingerCompactlySupported (hψ : IsLocallyConstant ψ)
    (hB : ∀ y, Continuous fun u ↦ B u y) :
    Representation k
      (⅟(2 : R) • (B.polarizedForm - B.polarizedForm.flip)).bilinearFactorSet.Extension
      (LocallyConstant.compactlySupported k X V) where
  toFun p :=
    { toFun := schroedingerCompactlySupportedAux hψ hB p
      map_add' f g := LocallyConstant.compactlySupported.coeFn_injective <| by
        simp [coe_schroedingerCompactlySupportedAux]
      map_smul' c f := LocallyConstant.compactlySupported.coeFn_injective <| by
        simp [coe_schroedingerCompactlySupportedAux] }
  map_one' := LinearMap.ext fun f ↦ LocallyConstant.compactlySupported.coeFn_injective <| by
    simp [coe_schroedingerCompactlySupportedAux]
  map_mul' p q := LinearMap.ext fun f ↦ LocallyConstant.compactlySupported.coeFn_injective <| by
    simp [coe_schroedingerCompactlySupportedAux]

/-- The operators of the Schwartz–Bruhat Schrödinger representation are those of
`LinearMap.schroedinger`. -/
@[simp]
theorem schroedingerCompactlySupported_apply (hψ : IsLocallyConstant ψ)
    (hB : ∀ y, Continuous fun u ↦ B u y)
    (p : (⅟(2 : R) • (B.polarizedForm - B.polarizedForm.flip)).bilinearFactorSet.Extension)
    (f : LocallyConstant.compactlySupported k X V) :
    ⇑(B.schroedingerCompactlySupported ψ V hψ hB p f : LocallyConstant X V) =
      B.schroedinger ψ V p f.val :=
  coe_schroedingerCompactlySupportedAux hψ hB p f

end CompactlySupported

/-! ### Unitarity -/

section Norm

variable {k V : Type*} [NormedField k] [SeminormedAddCommGroup V] [NormedSpace k V]
  {B : X →ₗ[R] Y →ₗ[R] C} {ψ : AddChar C k}

/-- For a unitary character `ψ`, the polarized Schrödinger operators act on norms by translation. -/
theorem norm_polarizedSchroedinger_apply (hψ : ∀ c, ‖ψ c‖ = 1)
    (p : B.polarizedForm.bilinearFactorSet.Extension) (φ : X → V) (u : X) :
    ‖B.polarizedSchroedinger ψ V p φ u‖ = ‖φ (u + p.right.toAdd.1)‖ := by
  simp [norm_smul, hψ]

/-- For a unitary character `ψ` and a translation-invariant measure on `X`, the polarized
Schrödinger operators preserve the integral of `‖φ‖ ^ 2`. -/
theorem integral_norm_sq_polarizedSchroedinger_apply [MeasurableSpace X] [MeasurableAdd X]
    (hψ : ∀ c, ‖ψ c‖ = 1) (μ : Measure X) [μ.IsAddRightInvariant]
    (p : B.polarizedForm.bilinearFactorSet.Extension) (φ : X → V) :
    ∫ u, ‖B.polarizedSchroedinger ψ V p φ u‖ ^ 2 ∂μ = ∫ u, ‖φ u‖ ^ 2 ∂μ := by
  simp_rw [norm_polarizedSchroedinger_apply hψ]
  exact integral_add_right_eq_self (fun u ↦ ‖φ u‖ ^ 2) _

variable [Invertible (2 : R)]

/-- For a unitary character `ψ`, the Schrödinger operators act on norms by translation. -/
theorem norm_schroedinger_apply (hψ : ∀ c, ‖ψ c‖ = 1)
    (p : (⅟(2 : R) • (B.polarizedForm - B.polarizedForm.flip)).bilinearFactorSet.Extension)
    (φ : X → V) (u : X) :
    ‖B.schroedinger ψ V p φ u‖ = ‖φ (u + p.right.toAdd.1)‖ := by
  rw [schroedinger_eq_polarizedSchroedinger, norm_polarizedSchroedinger_apply hψ,
    BilinMap.polarizationEquiv_apply]

/-- For a unitary character `ψ` and a translation-invariant measure on `X`, the Schrödinger
operators preserve the integral of `‖φ‖ ^ 2`: `∫ ‖ρψ(h) φ‖ ^ 2 = ∫ ‖φ‖ ^ 2`. No measurability of
`φ` is needed. This is the input for the unitarity of the operators on `L²`. -/
theorem integral_norm_sq_schroedinger_apply [MeasurableSpace X] [MeasurableAdd X]
    (hψ : ∀ c, ‖ψ c‖ = 1) (μ : Measure X) [μ.IsAddRightInvariant]
    (p : (⅟(2 : R) • (B.polarizedForm - B.polarizedForm.flip)).bilinearFactorSet.Extension)
    (φ : X → V) :
    ∫ u, ‖B.schroedinger ψ V p φ u‖ ^ 2 ∂μ = ∫ u, ‖φ u‖ ^ 2 ∂μ := by
  rw [schroedinger_eq_polarizedSchroedinger]
  exact integral_norm_sq_polarizedSchroedinger_apply hψ μ _ φ

end Norm

end LinearMap
