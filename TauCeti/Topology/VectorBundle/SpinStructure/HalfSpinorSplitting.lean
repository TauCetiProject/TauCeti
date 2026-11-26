/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.SpinStructure.Spinor
import TauCeti.LinearAlgebra.Alternating.TopDegree

/-!
# The splitting of a half-spinor bundle by a nonvanishing section

Let `s` be a `Spinᶜ` structure of rank four whose half-spinor bundle `W^ε`
(`TauCeti.SpinCStructure.halfSpinorBundle`) has complex rank two, with determinant line `L`
(`TauCeti.SpinCStructure.determinantLine`), and let `ω` be a nonzero alternating form on the model
half-spinors, so that `(ψ₁, ψ₂) ↦ ω(ψ₁, ψ₂)` descends to the alternating map
`W^ε_x × W^ε_x → L_x` identifying `⋀² W^ε_x` with `L_x`
(`TauCeti.SpinCStructure.halfSpinorDetAlternatingMap`,
`TauCeti.SpinCStructure.exteriorPowerHalfSpinorEquiv`). This file shows that a nonzero vector
`v ∈ W^ε_x` splits the fibre as `W^ε_x ≃ ℂ ⊕ L_x`, the line spanned by `v` and its complement:

`ψ ↦ (⟪v, ψ⟫, ω(v, ψ))`

is a complex linear isomorphism `W^ε_x ≃ ℂ × L_x` (`TauCeti.SpinCStructure.halfSpinorEquivProd`).
It sends `v` to `(‖v‖², 0)` (`TauCeti.SpinCStructure.halfSpinorEquivProd_self`). The second
component vanishes exactly on the line of `v`, because a nonzero alternating form of degree two on
a space of dimension two vanishes on `(v, ψ)` only when `ψ` is a multiple of `v`
(`TauCeti.SpinCStructure.halfSpinorDetAlternatingMap_eq_zero_iff`, from
`AlternatingMap.map_eq_zero_iff_exists_smul_eq`), and the first vanishes on the orthogonal
complement of `v`; so the map is injective, and both sides have complex dimension two.

A nowhere-vanishing section `u` of `W^ε` thus splits every fibre as `ℂ ⊕ L`, and when `u` is
continuous the two components of the splittings by its values are continuous on the total space
of `W^ε` (`TauCeti.SpinCStructure.continuous_fst_halfSpinorEquivProd`,
`TauCeti.SpinCStructure.continuous_snd_halfSpinorEquivProd`).

The inverse sends `(a, 0)` to `(a / ‖v‖²) • v`
(`TauCeti.SpinCStructure.halfSpinorEquivProd_symm_mk_zero`), so every `ψ` decomposes as
`ψ = (⟪v, ψ⟫ / ‖v‖²) v + β` with `β` in the complementary summand
(`TauCeti.SpinCStructure.smul_add_halfSpinorEquivProd_symm_zero`).

For the canonical `Spinᶜ` structure of an almost Hermitian four-manifold and its canonical spinor
`u₀`, this splits each fibre `W⁺_x` as `ℂ ⊕ K⁻¹_x`, the line spanned by `u₀(x)` and the fibre of
the anticanonical line, in which Taubes writes a positive spinor as `α u₀ + β`
(`TauCeti.OrthonormalFrameBundle.canonicalHalfSpinorEquivProd`, in
`TauCeti.Analysis.PDE.SeibergWitten.Bundle.CanonicalSpinor`). Only the forward components are
shown continuous; the bundle isomorphism `W⁺ ≃ 1 ⊕ K⁻¹` and the subbundle `K⁻¹ ⊂ W⁺` are not
constructed here.

## Main definitions

* `TauCeti.SpinCStructure.halfSpinorEquivProd`: the isomorphism `W^ε_x ≃ ℂ × L_x`,
  `ψ ↦ (⟪v, ψ⟫, ω(v, ψ))`, of a nonzero vector `v ∈ W^ε_x`.

## Main results

* `TauCeti.SpinCStructure.halfSpinorDetAlternatingMap_eq_zero_iff`: `ω(v, ψ) = 0` for a nonzero
  `v` exactly when `ψ` is a multiple of `v`.
* `TauCeti.SpinCStructure.halfSpinorEquivProd_apply`,
  `TauCeti.SpinCStructure.halfSpinorEquivProd_self`: the formula of the splitting, and its value
  `(‖v‖², 0)` on `v`.
* `TauCeti.SpinCStructure.halfSpinorEquivProd_symm_mk_zero`,
  `TauCeti.SpinCStructure.smul_add_halfSpinorEquivProd_symm_zero`: the inverse on the trivial
  summand, and the decomposition `ψ = (⟪v, ψ⟫ / ‖v‖²) v + β`.
* `TauCeti.SpinCStructure.continuous_fst_halfSpinorEquivProd`,
  `TauCeti.SpinCStructure.continuous_snd_halfSpinorEquivProd`: for a continuous nowhere-vanishing
  section, continuity of the two components on total spaces.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989,
  Appendix D.
* C. Okonek and A. Teleman, *Seiberg–Witten invariants and the Van de Ven conjecture*, 1995, §5.
-/

public section

noncomputable section

open Bundle Module Module.End TauCeti CliffordAlgebra TauCeti.CliffordAlgebra
open scoped InnerProductSpace

universe w

namespace TauCeti.SpinCStructure

variable {X : Type*} [TopologicalSpace X] {F : Type*} {E : X → Type w}
  [TopologicalSpace (TotalSpace F E)]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (finrank ℝ V = 4)] {Q : QuadraticForm ℝ V}
  {o : Orientation ℝ V (Fin 4)} {hQ : ∀ v, Q v = -‖v‖ ^ 2}
  {b : OrthonormalBasis (Fin 4) ℝ V}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}
  {hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)} {ε : ℂ}
  {h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) ε) = 2} {s : SpinCStructure F E 4}
  {ω : o.HalfSpinModel hQ b ρ hρ ε [⋀^Fin 2]→ₗ[ℂ] ℂ} {u : ∀ x, s.halfSpinorBundle o hQ b ρ hρ ε x}

/-- The proof that the standard form on `ℝ⁴` is nonzero, on which `Spinᶜ(4)` depends. -/
local notation "hpos" => QuadraticMap.Nondegenerate.ne_zero (nondegenerate_realCliffordForm 4 0)
local notation "SpinC" => spinCGroup (realCliffordForm 4 0) hpos

/-- **The determinant pairing vanishes exactly on parallel pairs.** For a nonzero alternating form
`ω` on the model half-spinors of complex dimension two and a nonzero `v ∈ W^ε_x`, the determinant
pairing `ω(v, ψ) ∈ L_x` vanishes exactly when `ψ` is a multiple of `v`. -/
theorem halfSpinorDetAlternatingMap_eq_zero_iff (hω : ω ≠ 0) {x : X}
    {v : s.halfSpinorBundle o hQ b ρ hρ ε x} (hv : v ≠ 0) (ψ : s.halfSpinorBundle o hQ b ρ hρ ε x) :
    s.halfSpinorDetAlternatingMap h₂ ω x ![v, ψ] = 0 ↔ ∃ a : ℂ, a • v = ψ := by
  obtain ⟨p⟩ := s.nonempty_P x
  have hmk := (AssociatedBundle.mk_bijective (G := SpinC) (F := o.HalfSpinModel hQ b ρ hρ ε) p).1
  obtain ⟨v, rfl⟩ := (AssociatedBundle.mk_bijective (G := SpinC) p).2 v
  obtain ⟨φ, rfl⟩ := (AssociatedBundle.mk_bijective (G := SpinC) p).2 ψ
  have hv₀ : v ≠ 0 := by
    rintro rfl
    exact hv (AssociatedBundle.mk_zero (G := SpinC) p)
  -- Read the pairing in the frame `p`, where it is the model form `ω`.
  rw [halfSpinorDetAlternatingMap_mk_mk, ← AssociatedBundle.mk_zero (G := SpinC) p,
    (AssociatedBundle.mk_bijective (G := SpinC) p).1.eq_iff, LinearIsometryEquiv.map_eq_zero_iff,
    AlternatingMap.map_eq_zero_iff_exists_smul_eq
      (Orientation.HalfSpinModel.toEigenspace.finrank_eq.trans h₂) hω hv₀]
  simp only [← AssociatedBundle.mk_smul_scalar, hmk.eq_iff]

variable (h₂ s ω) in
/-- The continuous linear map `ψ ↦ (⟪v, ψ⟫, ω(v, ψ))` underlying
`TauCeti.SpinCStructure.halfSpinorEquivProd`. -/
private def halfSpinorProdMap {x : X} (v : s.halfSpinorBundle o hQ b ρ hρ ε x) :
    s.halfSpinorBundle o hQ b ρ hρ ε x →L[ℂ] ℂ × s.determinantLine x :=
  (innerSL ℂ v).prod (AssociatedBundle.bilinearMap (P := s.P) (halfSpinorDetPairing ω)
    (halfSpinorDetPairing_smul_smul h₂ ω) x v)

private theorem halfSpinorProdMap_apply {x : X} (v ψ : s.halfSpinorBundle o hQ b ρ hρ ε x) :
    halfSpinorProdMap h₂ s ω v ψ = (⟪v, ψ⟫_ℂ, s.halfSpinorDetAlternatingMap h₂ ω x ![v, ψ]) := by
  rw [halfSpinorProdMap, ContinuousLinearMap.prod_apply, innerSL_apply_apply,
    bilinearMap_halfSpinorDetPairing_apply]

private theorem injective_halfSpinorProdMap (hω : ω ≠ 0) {x : X}
    {v : s.halfSpinorBundle o hQ b ρ hρ ε x} (hv : v ≠ 0) :
    Function.Injective (halfSpinorProdMap h₂ s ω v) := by
  refine (injective_iff_map_eq_zero _).2 fun ψ hψ ↦ ?_
  rw [halfSpinorProdMap_apply, Prod.mk_eq_zero] at hψ
  obtain ⟨a, rfl⟩ := (halfSpinorDetAlternatingMap_eq_zero_iff hω hv ψ).1 hψ.2
  rw [inner_smul_right] at hψ
  rw [(mul_eq_zero.1 hψ.1).resolve_right (inner_self_ne_zero.2 hv), zero_smul]

private theorem bijective_halfSpinorProdMap (hω : ω ≠ 0) {x : X}
    {v : s.halfSpinorBundle o hQ b ρ hρ ε x} (hv : v ≠ 0) :
    Function.Bijective (halfSpinorProdMap h₂ s ω v :
      s.halfSpinorBundle o hQ b ρ hρ ε x →ₗ[ℂ] ℂ × s.determinantLine x) := by
  refine ⟨injective_halfSpinorProdMap hω hv,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1
      (injective_halfSpinorProdMap hω hv)⟩
  rw [finrank_halfSpinorBundle, h₂, Module.finrank_prod, finrank_self, finrank_determinantLine]

variable (h₂ s) in
/-- **The splitting of a half-spinor fibre by a nonzero vector.** For a `Spinᶜ` structure of rank
four whose half-spinors have complex rank two, a nonzero alternating form `ω` on the model
half-spinors and a nonzero `v ∈ W^ε_x`, the complex linear isomorphism `W^ε_x ≃ ℂ × L_x`,
`ψ ↦ (⟪v, ψ⟫, ω(v, ψ))` (`TauCeti.SpinCStructure.halfSpinorEquivProd_apply`), onto the trivial
line and the determinant line. Applied to the values of a continuous nowhere-vanishing section,
its components are continuous on total spaces
(`TauCeti.SpinCStructure.continuous_fst_halfSpinorEquivProd`,
`TauCeti.SpinCStructure.continuous_snd_halfSpinorEquivProd`). -/
def halfSpinorEquivProd (hω : ω ≠ 0) {x : X} {v : s.halfSpinorBundle o hQ b ρ hρ ε x}
    (hv : v ≠ 0) : s.halfSpinorBundle o hQ b ρ hρ ε x ≃L[ℂ] ℂ × s.determinantLine x :=
  (LinearEquiv.ofBijective (halfSpinorProdMap h₂ s ω v : _ →ₗ[ℂ] _)
    (bijective_halfSpinorProdMap hω hv)).toContinuousLinearEquiv

/-- The splitting by `v` sends `ψ` to `(⟪v, ψ⟫, ω(v, ψ))`. -/
@[simp]
theorem halfSpinorEquivProd_apply (hω : ω ≠ 0) {x : X} {v : s.halfSpinorBundle o hQ b ρ hρ ε x}
    (hv : v ≠ 0) (ψ : s.halfSpinorBundle o hQ b ρ hρ ε x) :
    s.halfSpinorEquivProd h₂ hω hv ψ =
      (⟪v, ψ⟫_ℂ, s.halfSpinorDetAlternatingMap h₂ ω x ![v, ψ]) := by
  simp only [halfSpinorEquivProd, LinearEquiv.coe_toContinuousLinearEquiv',
    LinearEquiv.ofBijective_apply, ContinuousLinearMap.coe_coe, halfSpinorProdMap_apply]

/-- **The vector spans the trivial summand**: the splitting by `v` sends `v` to `(‖v‖², 0)`. -/
theorem halfSpinorEquivProd_self (hω : ω ≠ 0) {x : X} {v : s.halfSpinorBundle o hQ b ρ hρ ε x}
    (hv : v ≠ 0) : s.halfSpinorEquivProd h₂ hω hv v = ((‖v‖ : ℂ) ^ 2, 0) := by
  rw [halfSpinorEquivProd_apply,
    (s.halfSpinorDetAlternatingMap h₂ ω x).map_eq_zero_of_eq ![v, v] (i := 0) (j := 1) rfl
      zero_ne_one]
  simp

/-- **The inverse of the splitting on the trivial summand**: the splitting by `v` sends
`(a / ‖v‖²) • v` to `(a, 0)`. -/
@[simp]
theorem halfSpinorEquivProd_symm_mk_zero (hω : ω ≠ 0) {x : X}
    {v : s.halfSpinorBundle o hQ b ρ hρ ε x} (hv : v ≠ 0) (a : ℂ) :
    (s.halfSpinorEquivProd h₂ hω hv).symm (a, 0) = (a / (‖v‖ : ℂ) ^ 2) • v := by
  rw [ContinuousLinearEquiv.symm_apply_eq, map_smul, halfSpinorEquivProd_self]
  simp [hv]

/-- **The inverse of the splitting, trivial component**: `(s.halfSpinorEquivProd h₂ hω hv).symm z`
has inner product `z.1` with `v`; in particular the complementary summand `symm (0, l)` is
orthogonal to `v`. -/
@[simp]
theorem inner_halfSpinorEquivProd_symm (hω : ω ≠ 0) {x : X}
    {v : s.halfSpinorBundle o hQ b ρ hρ ε x} (hv : v ≠ 0) (z : ℂ × s.determinantLine x) :
    ⟪v, (s.halfSpinorEquivProd h₂ hω hv).symm z⟫_ℂ = z.1 := by
  simpa using congrArg Prod.fst
    (halfSpinorEquivProd_apply (h₂ := h₂) hω hv ((s.halfSpinorEquivProd h₂ hω hv).symm z)).symm

/-- **The inverse of the splitting, determinant-line component**: the determinant pairing of `v`
with `(s.halfSpinorEquivProd h₂ hω hv).symm z` is `z.2`. -/
@[simp]
theorem halfSpinorDetAlternatingMap_halfSpinorEquivProd_symm (hω : ω ≠ 0) {x : X}
    {v : s.halfSpinorBundle o hQ b ρ hρ ε x} (hv : v ≠ 0) (z : ℂ × s.determinantLine x) :
    s.halfSpinorDetAlternatingMap h₂ ω x ![v, (s.halfSpinorEquivProd h₂ hω hv).symm z] = z.2 := by
  simpa using congrArg Prod.snd
    (halfSpinorEquivProd_apply (h₂ := h₂) hω hv ((s.halfSpinorEquivProd h₂ hω hv).symm z)).symm

/-- **The decomposition along `v`**: every `ψ ∈ W^ε_x` is `α v + β`, with `α = ⟪v, ψ⟫ / ‖v‖²` and
`β` the vector of the complementary summand whose determinant-line component is `ω(v, ψ)`
(`TauCeti.SpinCStructure.halfSpinorEquivProd_apply`). -/
theorem smul_add_halfSpinorEquivProd_symm_zero (hω : ω ≠ 0) {x : X}
    {v : s.halfSpinorBundle o hQ b ρ hρ ε x} (hv : v ≠ 0)
    (ψ : s.halfSpinorBundle o hQ b ρ hρ ε x) :
    ((s.halfSpinorEquivProd h₂ hω hv ψ).1 / (‖v‖ : ℂ) ^ 2) • v +
        (s.halfSpinorEquivProd h₂ hω hv).symm (0, (s.halfSpinorEquivProd h₂ hω hv ψ).2) = ψ := by
  apply (s.halfSpinorEquivProd h₂ hω hv).injective
  rw [← halfSpinorEquivProd_symm_mk_zero (h₂ := h₂) hω hv, map_add,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply, Prod.mk_add_mk,
    add_zero, zero_add]

/-- **The trivial component of the splitting is continuous** on the total space of `W^ε`, for the
splittings by the values of a continuous nowhere-vanishing section `u`. -/
theorem continuous_fst_halfSpinorEquivProd (hω : ω ≠ 0) (hu : ∀ x, u x ≠ 0)
    (hc : Continuous fun x ↦ TotalSpace.mk' (o.HalfSpinModel hQ b ρ hρ ε) x (u x)) :
    Continuous fun z : TotalSpace (o.HalfSpinModel hQ b ρ hρ ε) (s.halfSpinorBundle o hQ b ρ hρ ε) ↦
      (s.halfSpinorEquivProd h₂ hω (hu z.proj) z.snd).1 := by
  simp only [halfSpinorEquivProd_apply]
  exact (hc.comp (FiberBundle.continuous_proj _ _)).inner_bundle_of_continuousFiberNorm
    continuous_id

/-- **The determinant-line component of the splitting is continuous** from the total space of
`W^ε` to that of `L`, for the splittings by the values of a continuous nowhere-vanishing section
`u`. -/
theorem continuous_snd_halfSpinorEquivProd (hω : ω ≠ 0) (hu : ∀ x, u x ≠ 0)
    (hc : Continuous fun x ↦ TotalSpace.mk' (o.HalfSpinModel hQ b ρ hρ ε) x (u x)) :
    Continuous fun z : TotalSpace (o.HalfSpinModel hQ b ρ hρ ε) (s.halfSpinorBundle o hQ b ρ hρ ε) ↦
      TotalSpace.mk' (DeterminantModel 4) z.proj
        (s.halfSpinorEquivProd h₂ hω (hu z.proj) z.snd).2 := by
  refine ((hc.comp (FiberBundle.continuous_proj _ _)).associatedBundleBilinearMap
    (halfSpinorDetPairing ω) (halfSpinorDetPairing_smul_smul h₂ ω) (w := fun z ↦ z.snd)
    continuous_id).congr fun z ↦ ?_
  rw [halfSpinorEquivProd_apply, bilinearMap_halfSpinorDetPairing_apply]

end TauCeti.SpinCStructure
