/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.EulerCharacteristic
public import TauCeti.AlgebraicGeometry.LineBundle.Class

/-!
# The Euler-characteristic degree of a line bundle

On a proper curve over a field, the degree of a line bundle `L` can be recovered from Euler
characteristics by

`deg L = χ(L) - χ(𝒪_X)`.

This file constructs the right-hand side using the degree-`2` truncation of sheaf cohomology and
shows that it depends only on the isomorphism class of `L`. Thus it descends to a function
`LineBundleClass.eulerDegree k : LineBundleClass X → ℤ`. The normalization by the trivial line
bundle makes its degree zero by construction.

The definition makes sense for any scheme over a field. As with `Scheme.Modules.eulerCharBelow`,
it is the difference of the usual Euler characteristics when the relevant cohomology groups are
finite-dimensional and cohomology above degree one vanishes. On a proper curve with
`H¹(X, 𝒪_X)` finite-dimensional, `TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.EulerCharacteristic`
identifies this invariant with the residue-degree-weighted degree of a divisor of `L` and proves
that it is additive.

## Main declarations

* `InvertibleSheaf.eulerDegree` is `χ(L) - χ(𝒪_X)` for an invertible sheaf;
* `InvertibleSheaf.eulerDegree_def` is its defining formula;
* `InvertibleSheaf.eulerDegree_eq_sub_unit` states it with the structure sheaf `𝒪_X` in place
  of the trivial line bundle;
* `InvertibleSheaf.eulerDegree_eq_finrank_sub` expands it as the difference of the dimensions of
  `H⁰` and `H¹`;
* `LineBundleClass.eulerDegree` descends the invariant to isomorphism classes of line bundles;
* `LineBundleClass.eulerDegree_mk` and `LineBundleClass.eulerDegree_one` are its representative
  and normalization formulas.

The formula is the rearrangement of Riemann--Roch for curves; see Hartshorne, *Algebraic
Geometry*, Chapter IV, Section 1.
-/

public section

open AlgebraicGeometry CategoryTheory
open Module (finrank)

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace InvertibleSheaf

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- The Euler-characteristic degree `χ(L) - χ(𝒪_X)` of an invertible sheaf `L`, using the
degree-`2` truncation `χ(M) = dim H⁰(X, M) - dim H¹(X, M)`.

For a proper curve, finite-dimensionality and vanishing above degree one make this the usual
Euler characteristic degree. No such hypotheses are needed to form the invariant itself; in
their absence it has the same possible junk values as `Scheme.Modules.eulerCharBelow`. -/
def eulerDegree (L : InvertibleSheaf X) : ℤ :=
  Scheme.Modules.eulerCharBelow k X L.obj 2 -
    Scheme.Modules.eulerCharBelow k X (trivial X).obj 2

/-- The defining formula of the Euler-characteristic degree as a difference of truncated Euler
characteristics. -/
lemma eulerDegree_def (L : InvertibleSheaf X) :
    L.eulerDegree k =
      Scheme.Modules.eulerCharBelow k X L.obj 2 -
        Scheme.Modules.eulerCharBelow k X (trivial X).obj 2 :=
  (rfl)

/-- The Euler-characteristic degree is `χ(L) - χ(𝒪_X)` with `𝒪_X` the structure sheaf. -/
lemma eulerDegree_eq_sub_unit (L : InvertibleSheaf X) :
    L.eulerDegree k =
      Scheme.Modules.eulerCharBelow k X L.obj 2 -
        Scheme.Modules.eulerCharBelow k X (SheafOfModules.unit X.ringCatSheaf) 2 := by
  rw [eulerDegree_def]
  congr 1
  rw [trivial_obj]
  exact Scheme.Modules.eulerCharBelow_congr (X := X) k
    (TauCeti.SheafOfModules.freePUnitIsoUnit _) 2

/-- The Euler-characteristic degree is the difference of `dim H⁰ - dim H¹` for the line bundle
and the trivial line bundle. -/
lemma eulerDegree_eq_finrank_sub (L : InvertibleSheaf X) :
    L.eulerDegree k =
      ((finrank k (Scheme.Modules.Cohomology L.obj 0) : ℤ) -
          (finrank k (Scheme.Modules.Cohomology L.obj 1) : ℤ)) -
        ((finrank k (Scheme.Modules.Cohomology (trivial X).obj 0) : ℤ) -
          (finrank k (Scheme.Modules.Cohomology (trivial X).obj 1) : ℤ)) := by
  rw [eulerDegree_def, Scheme.Modules.eulerCharBelow_two,
    Scheme.Modules.eulerCharBelow_two]

/-- Isomorphic invertible sheaves have the same Euler-characteristic degree. -/
lemma eulerDegree_congr {L M : InvertibleSheaf X} (e : L.obj ≅ M.obj) :
    L.eulerDegree k = M.eulerDegree k := by
  rw [eulerDegree_def, eulerDegree_def]
  congr 1
  exact Scheme.Modules.eulerCharBelow_congr k e 2

/-- The trivial line bundle has Euler-characteristic degree zero. -/
@[simp]
lemma eulerDegree_trivial : (trivial X).eulerDegree k = 0 := by
  rw [eulerDegree_def, sub_self]

end InvertibleSheaf

namespace LineBundleClass

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- The Euler-characteristic degree of an isomorphism class of line bundles.

This is well defined because sheaf cohomology, and hence its truncated Euler characteristic, is
invariant under isomorphism of coefficient sheaves. -/
def eulerDegree (a : LineBundleClass X) : ℤ :=
  lift (InvertibleSheaf.eulerDegree k)
    (fun _ _ h ↦ h.elim (InvertibleSheaf.eulerDegree_congr k)) a

/-- The Euler-characteristic degree of the class represented by `L` is the degree of `L`. -/
@[simp]
lemma eulerDegree_mk (L : InvertibleSheaf X) :
    eulerDegree k (mk L) = L.eulerDegree k :=
  lift_mk L

/-- The tensor-unit class has Euler-characteristic degree zero. -/
@[simp]
lemma eulerDegree_one : eulerDegree k (1 : LineBundleClass X) = 0 := by
  rw [← mk_trivial, eulerDegree_mk, InvertibleSheaf.eulerDegree_trivial]

end LineBundleClass

end

end AlgebraicGeometry

end TauCeti
