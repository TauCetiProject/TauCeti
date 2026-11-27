/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DeligneTorus.Hodge
public import TauCeti.Algebra.AlgebraicGroup.DeligneTorus.MumfordTate.Basic

/-!
# The subspaces stable under the Mumford–Tate group

Let `G` be an affine group over `ℚ` with coordinate Hopf algebra `H`, let `M` be a representation
of `G` (a right `H`-comodule), and let `h : S → G_ℝ` be a homomorphism from the Deligne torus.
Through `h`, the real representation `ℝ ⊗[ℚ] M` of `G_ℝ` becomes a representation of `S`
(`TauCeti.DeligneTorus.realComodule`), whose complexification splits into the Hodge components
`V^{p,q}` (`TauCeti.DeligneTorus.hodgeComponent`), the weight spaces of `S_ℂ`. No condition on
`h` is imposed here. When `G = GL(V)` for a finite-dimensional `ℚ`-vector space `V`, `M = V`,
and the weight cocharacter of `h` is defined over `ℚ`, this decomposition is the rational Hodge
structure on `V` defined by `h`.

This file proves that a rational subspace `W ≤ M` is stable under the Mumford–Tate group `MT(h)`
(its stabilizer in `G` contains `MT(h)`, that is, its stabilizer Hopf ideal lies below the
Mumford–Tate ideal) exactly when `ℂ ⊗ W` is the sum of its intersections with the `V^{p,q}`. In
the `GL(V)` setting above the latter says that `W` is a sub-Hodge structure, so the sub-Hodge
structures are exactly the subspaces stable under `MT(h)`.

The proof goes through the real subrepresentations of `S`. If `W` is a sub-Hodge structure, then
`W_ℝ` is a subrepresentation of `S`, so `h` factors through the real extension of the stabilizer
of `W`, a closed `ℚ`-subgroup; by minimality it contains `MT(h)`. Conversely, if `MT(h)`
stabilizes `W`, so does `h(S)`, which factors through the real extension of `MT(h)`.

## Main declarations

* `TauCeti.DeligneTorus.realComodule M h`: the representation of `S` on `ℝ ⊗[ℚ] M` through `h`.
* `TauCeti.DeligneTorus.stabilizerHopfIdeal_le_mumfordTateHopfIdeal_iff`: `MT(h)` stabilizes `W`
  exactly when `W_ℝ` is a subrepresentation of `S`.
* `TauCeti.DeligneTorus.stabilizerHopfIdeal_le_mumfordTateHopfIdeal_iff_eq_iSup_inf_hodgeComponent`:
  **`MT(h)` stabilizes `W` exactly when `ℂ ⊗ W` is the sum of its intersections with the
  `V^{p,q}`**, that is, in the `GL(V)` setting above, when `W` is a sub-Hodge structure.

## References

* J. S. Milne, *Introduction to Shimura varieties*, §2, p. 31 (the aside after Definition 2.16).
* P. Deligne, *Hodge cycles on abelian varieties* (notes by J. S. Milne), §3, pp. 24–25.
-/

public section

open CategoryTheory TauCeti.CommHopfAlgCat
open scoped TensorProduct

namespace TauCeti.DeligneTorus

section Representation

variable {H : _root_.CommHopfAlgCat.{0} ℚ} (M : Type*) [AddCommMonoid M] [Module ℚ M]
  [Comodule ℚ H M]

/-- **The real representation of `S` defined by `h`**: the real extension `ℝ ⊗[ℚ] M` of a
representation `M` of `G`, a representation of `G_ℝ`, restricted to the Deligne torus along
`h : S → G_ℝ`. For `G = GL(V)` with `V` finite-dimensional, `M = V`, and the weight cocharacter
of `h` defined over `ℚ`, its Hodge components are those of the rational Hodge structure on `V`
defined by `h`. -/
@[instance_reducible]
noncomputable def realComodule (h : baseChange (K := ℝ) H ⟶ _root_.CommHopfAlgCat.of ℝ S) :
    Comodule ℝ S (ℝ ⊗[ℚ] M) :=
  letI := Comodule.baseChange (R := ℚ) (H := H) (M := M) ℝ
  Comodule.Corestrict h.hom.toCoalgHom

/-- `realComodule M h` is the real extension of `M` corestricted along `h`. -/
theorem realComodule_def (h : baseChange (K := ℝ) H ⟶ _root_.CommHopfAlgCat.of ℝ S) :
    realComodule M h =
      letI := Comodule.baseChange (R := ℚ) (H := H) (M := M) ℝ
      Comodule.Corestrict h.hom.toCoalgHom :=
  (rfl)

end Representation

variable {H : _root_.CommHopfAlgCat.{0} ℚ} {M : Type*} [AddCommGroup M] [Module ℚ M]
  [Comodule ℚ H M]

/-- **`MT(h)` stabilizes `W` exactly when `W_ℝ` is stable under `S`.** The stabilizer in `G` of a
rational subspace `W ≤ M` contains the Mumford–Tate group of `h` exactly when `ℝ ⊗[ℚ] W` is a
subrepresentation of the representation of `S` defined by `h`, that is, when its stabilizer in
`S` is all of `S`. -/
theorem stabilizerHopfIdeal_le_mumfordTateHopfIdeal_iff
    (h : baseChange (K := ℝ) H ⟶ _root_.CommHopfAlgCat.of ℝ S) (W : Submodule ℚ M) :
    letI := realComodule M h
    W.stabilizerHopfIdeal H ≤ mumfordTateHopfIdeal h ↔
      (W.baseChange ℝ).stabilizerHopfIdeal S = ⊥ := by
  let _ := Comodule.baseChange (R := ℚ) (H := H) (M := M) ℝ
  -- `S` is a `ℚ`-algebra through `ℝ`, to read points of `G_ℝ` with values in `S` as points of `G`
  let _ : Algebra ℚ S := Algebra.compHom S (algebraMap ℚ ℝ)
  have _ : IsScalarTower ℚ ℝ S := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  rw [le_mumfordTateHopfIdeal_iff, baseChangeHopfIdeal_toIdeal, Ideal.map_le_iff_le_comap,
    realComodule, Submodule.stabilizerHopfIdeal_corestrict_eq_bot_iff,
    Submodule.stabilizerHopfIdeal_baseChange_le_ker_iff, ← AlgHom.comap_ker]
  -- the kernels of `h` and of its restriction of scalars to `ℚ` are the same ideal
  have hker : RingHom.ker (AlgHom.restrictScalars ℚ (h.hom : ℝ ⊗[ℚ] H →ₐ[ℝ] S)) =
      RingHom.ker (h.hom : ℝ ⊗[ℚ] H →ₐ[ℝ] S).toRingHom := by
    ext x
    simp only [RingHom.mem_ker, AlgHom.restrictScalars_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe]
  rw [hker]

/-- **The subspaces stable under the Mumford–Tate group.** The stabilizer in `G` of a rational
subspace `W ≤ M` contains `MT(h)` exactly when the complexification `ℂ ⊗[ℝ] (ℝ ⊗[ℚ] W)` is the
sum of its intersections with the Hodge components `V^{p,q}` of the representation of `S` defined
by `h`. When `G = GL(V)` with `V` finite-dimensional, `M = V`, and the weight cocharacter of `h` is
defined over `ℚ`, so that `h` defines a rational Hodge structure on `V`, this says that the
sub-Hodge structures of `V` are exactly the subspaces stable under `MT(h)`. -/
theorem stabilizerHopfIdeal_le_mumfordTateHopfIdeal_iff_eq_iSup_inf_hodgeComponent
    (h : baseChange (K := ℝ) H ⟶ _root_.CommHopfAlgCat.of ℝ S) (W : Submodule ℚ M) :
    letI := realComodule M h
    W.stabilizerHopfIdeal H ≤ mumfordTateHopfIdeal h ↔
      (W.baseChange ℝ).baseChange ℂ =
        ⨆ pq : ℤ × ℤ, (W.baseChange ℝ).baseChange ℂ ⊓ hodgeComponent (ℝ ⊗[ℚ] M) pq.1 pq.2 := by
  let _ := realComodule M h
  rw [stabilizerHopfIdeal_le_mumfordTateHopfIdeal_iff,
    Submodule.stabilizerHopfIdeal_eq_bot_iff_eq_iSup_inf_hodgeComponent]

end TauCeti.DeligneTorus
