/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DeligneTorus.Coordinate
public import TauCeti.Algebra.AlgebraicGroup.DeligneTorus.MumfordTate.Basic

/-!
# The rational coordinate kernel of a homomorphism from the Deligne torus

Let `G` be an affine group over `ℚ` with coordinate Hopf algebra `H`, and let `h : S → G_ℝ` be a
homomorphism of real algebraic groups from the Deligne torus. Its comorphism
`ℝ ⊗[ℚ] H → O(S)` restricts along `x ↦ 1 ⊗ x` to a `ℚ`-algebra map `H → O(S)`
(`TauCeti.DeligneTorus.rationalCoordinateMap`). Its kernel `K_h`
(`TauCeti.DeligneTorus.rationalCoordinateKernel`) is the ideal of the rational functions on `G`
vanishing on `h(S)`, the ideal of the `ℚ`-Zariski closure of `h(S)`. It need not be a Hopf ideal.

The Mumford–Tate ideal is the largest Hopf ideal contained in `K_h`: a Hopf ideal `I` lies below
it exactly when `I ≤ K_h`, because `h` kills the real extension `I_ℝ` exactly when it kills `I`,
which spans `I_ℝ`.

The map `O(S) → ℂ ⊗[ℝ] O(S)` is injective, and `ℂ ⊗[ℝ] O(S)` is the group algebra `ℂ[ℤ²]` of the
split torus `S_ℂ ≅ 𝔾ₘ × 𝔾ₘ` (`TauCeti.DeligneTorus.splittingBialgEquiv`). So `K_h` is also the
kernel of the complexified split map `H → ℂ[z₁^{±1}, z₂^{±1}]`
(`TauCeti.DeligneTorus.complexSplitCoordinateMap`), and the Mumford–Tate ideal is the largest
Hopf ideal inside that kernel.

## Main declarations

* `TauCeti.DeligneTorus.rationalCoordinateKernel h`: the kernel `K_h` of `H → O(S)`.
* `TauCeti.DeligneTorus.le_mumfordTateHopfIdeal_iff_toIdeal_le_rationalCoordinateKernel`: a Hopf
  ideal lies below the Mumford–Tate ideal exactly when it lies in `K_h`.
* `TauCeti.DeligneTorus.mumfordTateHopfIdeal_toIdeal_le_rationalCoordinateKernel`: the
  Mumford–Tate ideal lies in `K_h`.
* `TauCeti.DeligneTorus.ker_complexSplitCoordinateMap`: `K_h` is the kernel of the complexified
  split map `H → ℂ[ℤ²]`.
* `TauCeti.DeligneTorus.le_mumfordTateHopfIdeal_iff_toIdeal_le_ker_complexSplitCoordinateMap`:
  the Mumford–Tate ideal is the largest Hopf ideal killed by the complexified split map.

## References

* J. S. Milne, *Introduction to Shimura varieties*, §2, Theorem 2.14, proof of (a), p. 30, and
  the aside after Definition 2.16, p. 31.
-/

public section

open CategoryTheory _root_.CommHopfAlgCat TauCeti.CommHopfAlgCat
open scoped TensorProduct

namespace TauCeti.DeligneTorus

variable {H : _root_.CommHopfAlgCat.{0} ℚ}

/-- The comorphism of `h : S → G_ℝ` restricted to the rational coordinate functions: the ring
map `H → ℝ ⊗[ℚ] H → O(S)`, `x ↦ h*(1 ⊗ x)`. -/
noncomputable def rationalCoordinateMap
    (h : baseChange (K := ℝ) H ⟶ _root_.CommHopfAlgCat.of ℝ S) : H →+* S :=
  h.hom.toAlgHom.toRingHom.comp
    (Algebra.TensorProduct.includeRight : H →ₐ[ℚ] ℝ ⊗[ℚ] H).toRingHom

/-- The rational coordinate map sends `x` to `h*(1 ⊗ x)`. -/
@[simp]
theorem rationalCoordinateMap_apply
    (h : baseChange (K := ℝ) H ⟶ _root_.CommHopfAlgCat.of ℝ S) (x : H) :
    rationalCoordinateMap h x = h.hom ((1 : ℝ) ⊗ₜ[ℚ] x) := by
  simp [rationalCoordinateMap]

/-- **The rational coordinate kernel** `K_h` of `h : S → G_ℝ`: the ideal of the rational
coordinate functions on `G` killed by `h`, the ideal of the `ℚ`-Zariski closure of `h(S)`. It
need not be a Hopf ideal; the Mumford–Tate ideal is the largest Hopf ideal it contains
(`TauCeti.DeligneTorus.le_mumfordTateHopfIdeal_iff_toIdeal_le_rationalCoordinateKernel`). -/
noncomputable def rationalCoordinateKernel
    (h : baseChange (K := ℝ) H ⟶ _root_.CommHopfAlgCat.of ℝ S) : Ideal H :=
  RingHom.ker (rationalCoordinateMap h)

/-- A rational coordinate function lies in `K_h` exactly when `h*(1 ⊗ x) = 0`. -/
@[simp]
theorem mem_rationalCoordinateKernel
    {h : baseChange (K := ℝ) H ⟶ _root_.CommHopfAlgCat.of ℝ S} {x : H} :
    x ∈ rationalCoordinateKernel h ↔ h.hom ((1 : ℝ) ⊗ₜ[ℚ] x) = 0 :=
  RingHom.mem_ker

/-- An ideal of `H` lies in `K_h` exactly when `h` kills its real extension. -/
theorem le_rationalCoordinateKernel_iff
    {h : baseChange (K := ℝ) H ⟶ _root_.CommHopfAlgCat.of ℝ S} {J : Ideal H} :
    J ≤ rationalCoordinateKernel h ↔
      J.map (Algebra.TensorProduct.includeRight : H →ₐ[ℚ] ℝ ⊗[ℚ] H) ≤
        RingHom.ker h.hom.toAlgHom.toRingHom := by
  simp only [rationalCoordinateKernel, rationalCoordinateMap, AlgHom.toRingHom_eq_coe]
  rw [Ideal.map_le_iff_le_comap, ← Ideal.comap_coe, RingHom.comap_ker]

/-- **The Mumford–Tate ideal is the largest Hopf ideal inside `K_h`.** A Hopf ideal of `H` lies
below the Mumford–Tate ideal of `h` exactly when it consists of rational functions vanishing on
`h(S)`. This is the rational form of `TauCeti.DeligneTorus.le_mumfordTateHopfIdeal_iff`. -/
theorem le_mumfordTateHopfIdeal_iff_toIdeal_le_rationalCoordinateKernel
    {h : baseChange (K := ℝ) H ⟶ _root_.CommHopfAlgCat.of ℝ S} {I : HopfIdeal ℚ H} :
    I ≤ mumfordTateHopfIdeal h ↔ I.toIdeal ≤ rationalCoordinateKernel h := by
  rw [le_mumfordTateHopfIdeal_iff, baseChangeHopfIdeal_toIdeal, le_rationalCoordinateKernel_iff]

/-- The Mumford–Tate ideal lies in `K_h`: every function in it vanishes on `h(S)`. -/
theorem mumfordTateHopfIdeal_toIdeal_le_rationalCoordinateKernel
    (h : baseChange (K := ℝ) H ⟶ _root_.CommHopfAlgCat.of ℝ S) :
    (mumfordTateHopfIdeal h).toIdeal ≤ rationalCoordinateKernel h :=
  le_mumfordTateHopfIdeal_iff_toIdeal_le_rationalCoordinateKernel.mp le_rfl

/-- **The complexified split coordinate map** of `h : S → G_ℝ`: the ring map
`H → O(S) → ℂ ⊗[ℝ] O(S) ≃ ℂ[ℤ²]` to the coordinate ring `ℂ[z₁^{±1}, z₂^{±1}]` of the split
torus `S_ℂ ≅ 𝔾ₘ × 𝔾ₘ`, through `TauCeti.DeligneTorus.splittingBialgEquiv`. -/
noncomputable def complexSplitCoordinateMap
    (h : baseChange (K := ℝ) H ⟶ _root_.CommHopfAlgCat.of ℝ S) :
    H →+* MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)) :=
  ((splittingBialgEquiv : ℂ ⊗[ℝ] S →ₐ[ℂ] MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ))).toRingHom.comp
    (Algebra.TensorProduct.includeRight : S →ₐ[ℝ] ℂ ⊗[ℝ] S).toRingHom).comp
    (rationalCoordinateMap h)

/-- The complexified split map sends `x` to the image of `h*(1 ⊗ x)` under
`TauCeti.DeligneTorus.splittingPoint`. -/
@[simp]
theorem complexSplitCoordinateMap_apply
    (h : baseChange (K := ℝ) H ⟶ _root_.CommHopfAlgCat.of ℝ S) (x : H) :
    complexSplitCoordinateMap h x = splittingPoint.ofConv (h.hom ((1 : ℝ) ⊗ₜ[ℚ] x)) := by
  simp [complexSplitCoordinateMap]

/-- **`K_h` from the complexified split map.** The rational coordinate kernel of `h` is the
kernel of the complexified split map `H → ℂ[z₁^{±1}, z₂^{±1}]`, because `O(S) → ℂ ⊗[ℝ] O(S)` is
injective. -/
@[simp]
theorem ker_complexSplitCoordinateMap
    (h : baseChange (K := ℝ) H ⟶ _root_.CommHopfAlgCat.of ℝ S) :
    RingHom.ker (complexSplitCoordinateMap h) = rationalCoordinateKernel h := by
  have hinj : Function.Injective
      (((splittingBialgEquiv : ℂ ⊗[ℝ] S →ₐ[ℂ] MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ))).toRingHom
        |>.comp (Algebra.TensorProduct.includeRight : S →ₐ[ℝ] ℂ ⊗[ℝ] S).toRingHom)) :=
    splittingBialgEquiv.injective.comp
      (Algebra.TensorProduct.includeRight_injective (algebraMap ℝ ℂ).injective)
  rw [complexSplitCoordinateMap, RingHom.ker_comp_of_injective _ hinj, rationalCoordinateKernel]

/-- **The Mumford–Tate ideal from the complexified split map.** A Hopf ideal of `H` lies below the
Mumford–Tate ideal of `h` exactly when the complexified split map
`H → ℂ[z₁^{±1}, z₂^{±1}]` kills it: the Mumford–Tate ideal is the largest Hopf ideal inside the
kernel of that map. -/
theorem le_mumfordTateHopfIdeal_iff_toIdeal_le_ker_complexSplitCoordinateMap
    {h : baseChange (K := ℝ) H ⟶ _root_.CommHopfAlgCat.of ℝ S} {I : HopfIdeal ℚ H} :
    I ≤ mumfordTateHopfIdeal h ↔ I.toIdeal ≤ RingHom.ker (complexSplitCoordinateMap h) := by
  rw [ker_complexSplitCoordinateMap,
    le_mumfordTateHopfIdeal_iff_toIdeal_le_rationalCoordinateKernel]

end TauCeti.DeligneTorus
