/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import TauCeti.Algebra.Homology.HomologicalComplex.ExtExactness
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import TauCeti.Algebra.Category.ModuleCat.Generator

/-!
# Testing exactness of finite projective cochains using regular coefficients

Vanishing of `Ext^j(M, R)` implies vanishing of `Ext^j(M, P)` for every finitely generated
projective `P`. Hence a nonnegative cochain complex of finitely generated projectives is
exact through degree `n` if `Ext^j(H^i, R)` vanishes whenever `j ≤ i ≤ n`.
In the dominant-dimension argument the complex is the regular dual of a projective resolution,
and the modules `H^i` are the regular-coefficient Ext groups on the opposite side.

## References

* M. Hoshino, *On dominant dimension of Noetherian rings*, Osaka J. Math. 26 (1989), 275–280,
  Lemma 2.1 and the final induction on p. 277.
-/

public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe u

namespace ModuleCat

variable {R : Type u} [Ring R]

/-- If `Ext^j(M, R)` vanishes, so does `Ext^j(M, P)` for a finitely generated
projective module `P`. -/
theorem subsingleton_ext_of_subsingleton_ext_regular {M P : ModuleCat.{u} R} {j : ℕ}
    [Module.Finite R P] [Projective P] (h : Subsingleton (Ext M (ModuleCat.of R R) j)) :
    Subsingleton (Ext M P j) := by
  obtain ⟨k, ⟨r⟩⟩ := ModuleCat.exists_retract_pi_of_projective P
  let F := extFunctorObj M j
  let e := ModuleCat.biproductIsoPi (fun _ : Fin k ↦ ModuleCat.of R R)
  have hsum : Subsingleton (Ext M (⨁ fun _ : Fin k ↦ ModuleCat.of R R) j) :=
    (Ext.addEquivBiproduct M (biproduct.isBilimit _) j).toEquiv.subsingleton
  have hfree := (AddCommGrpCat.isZero_iff_subsingleton.mpr hsum).of_iso (F.mapIso e.symm)
  exact AddCommGrpCat.isZero_iff_subsingleton.mp (IsZero.of_mono (r.map F).i hfree)

end ModuleCat

namespace CochainComplex

/-- A nonnegative cochain complex of left modules with finitely generated projective terms
through degree `n` is exact through degree `n` if `Ext^j(H^i, R)` vanishes whenever
`j ≤ i ≤ n`. The condition at `j = 0` means that `H^i` has zero regular dual. -/
theorem exactAt_of_subsingleton_ext_homology_regular {R : Type u} [Ring R]
    (K : CochainComplex (ModuleCat.{u} R) ℕ) {n : ℕ}
    (hfinite : ∀ i ≤ n, Module.Finite R (K.X i)) (hproj : ∀ i ≤ n, Projective (K.X i))
    (h : ∀ i ≤ n, ∀ j ≤ i, Subsingleton (Ext (K.homology i) (ModuleCat.of R R) j)) :
    ∀ i ≤ n, K.ExactAt i := by
  apply K.exactAt_of_subsingleton_ext_homology
  intro i hi j hj
  have := hfinite j (hj.trans hi)
  have := hproj j (hj.trans hi)
  exact ModuleCat.subsingleton_ext_of_subsingleton_ext_regular (h i hi (i - j) (Nat.sub_le ..))

end CochainComplex
