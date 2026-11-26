/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Module.Injective
public import TauCeti.Algebra.Homology.LinearHomComplex.Bidual
public import TauCeti.Algebra.Module.Injective.Bidual

import Mathlib.Algebra.Category.ModuleCat.Injective
import TauCeti.Algebra.Homology.LinearHomComplex.Single

/-!
# Biduality on the cohomology of complexes

For self-injective commutative coefficients, the Kronecker equivalence identifies the
cohomology of the dual complex with the dual of cohomology in the opposite degree. Applied
twice, it identifies `CochainComplex.bidualHom` on cohomology with signed evaluation.
Consequently this map is a quasi-isomorphism precisely when every cohomology module is
reflexive. Finitely presented cohomology suffices over a self-injective ring, as does finitely
generated cohomology over a Noetherian self-injective ring.
Since the coefficient complex `R[0]` is bounded below and consists of injectives, it is
K-injective, so this dual complex computes the derived coefficient dual.

The public equivalence `CochainComplex.linearDualHomologyEquiv` and its cocycle equation
`CochainComplex.linearDualHomologyEquiv_homologyπ` use
`CochainComplex.linearHomComplexSingleKroneckerEquiv` and its computation on cocycle classes.
The instance `CochainComplex.quasiIso_bidualHom` applies whenever the cohomology modules are
reflexive, including the finite-presentation and finite-module cases through
`Module.IsReflexive.of_injective_of_finitePresentation` and
`Module.IsReflexive.of_injective_of_finite`. This is the coefficient calculation underlying
biduality at a geometric point in SGA 4½, [Dualité], 1.1–1.4.
-/

public section

noncomputable section

open CategoryTheory HomologicalComplex

universe u

namespace CochainComplex

variable {R : Type u} [CommRing R] [Module.Injective R R]
  (K : CochainComplex (ModuleCat.{u} R) ℤ)

/-- Over self-injective coefficients, cohomology of the dual complex in degree `n` is the
dual of cohomology in degree `p = -n`. -/
def linearDualHomologyEquiv (p n : ℤ) (h : p + n = 0) :
    (linearDual R K).homology n ≃ₗ[R] Module.Dual R (K.homology p) :=
  letI := Module.injective_object_of_injective_module R R
  ((linearHomComplexSingleKroneckerEquiv R K (ModuleCat.of R R) n).trans
    ModuleCat.homLinearEquiv).trans
      (LinearEquiv.cast (M := fun p : ℤ ↦ Module.Dual R (K.homology p)) (by omega : -n = p))

/-- The dual-cohomology equivalence evaluates a cocycle class on a cocycle class by
evaluating the underlying dual cochain on the underlying cocycle. -/
@[simp]
theorem linearDualHomologyEquiv_homologyπ (p n : ℤ) (h : p + n = 0)
    (φ : (linearDual R K).cycles n) (x : K.cycles p) :
    linearDualHomologyEquiv K p n h ((linearDual R K).homologyπ n φ) (K.homologyπ p x) =
      linearDualXEquiv K h ((linearDual R K).iCycles n φ) (K.iCycles p x) := by
  obtain rfl : p = -n := by omega
  simp only [linearDualHomologyEquiv, LinearEquiv.trans_apply, LinearEquiv.cast_apply, cast_eq]
  rw [ModuleCat.homLinearEquiv_apply, AddEquiv.toFun_eq_coe, ModuleCat.homAddEquiv_apply]
  simpa only [linearHomComplexSingleKroneckerEquiv_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
    linearDualXEquiv_apply] using
    LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      (homologyπ_linearHomComplexSingleKronecker (k := R) K (ModuleCat.of R R) n φ)) x

/-- The double Kronecker identification of the cohomology of the bidual complex with the
bidual of the cohomology module. -/
def bidualHomologyEquiv (i : ℤ) :
    (linearDual R (linearDual R K)).homology i ≃ₗ[R]
      Module.Dual R (Module.Dual R (K.homology i)) :=
  (linearDualHomologyEquiv (linearDual R K) (-i) i (neg_add_cancel i)).trans
    (linearDualHomologyEquiv K i (-i) (add_neg_cancel i)).symm.dualMap

/-- The double Kronecker equivalence evaluates a bidual cocycle on a functional on
cohomology by evaluating it on any dual cocycle representing that functional. -/
theorem bidualHomologyEquiv_homologyπ (i : ℤ)
    (x : (linearDual R (linearDual R K)).cycles i)
    (f : Module.Dual R (K.homology i)) (φ : (linearDual R K).cycles (-i))
    (hφ : ∀ z : K.cycles i,
      linearDualXEquiv K (add_neg_cancel i) ((linearDual R K).iCycles (-i) φ)
        (K.iCycles i z) = f (K.homologyπ i z)) :
    bidualHomologyEquiv K i ((linearDual R (linearDual R K)).homologyπ i x) f =
      linearDualXEquiv (linearDual R K) (neg_add_cancel i)
        ((linearDual R (linearDual R K)).iCycles i x) ((linearDual R K).iCycles (-i) φ) := by
  have hφ' : linearDualHomologyEquiv K i (-i) (add_neg_cancel i)
      ((linearDual R K).homologyπ (-i) φ) = f := by
    apply K.moduleCat_linearMap_ext_homologyπ
    intro z
    exact (linearDualHomologyEquiv_homologyπ K i (-i) (add_neg_cancel i) φ z).trans (hφ z)
  simp only [bidualHomologyEquiv, LinearEquiv.trans_apply, LinearEquiv.dualMap_apply]
  rw [← hφ', LinearEquiv.symm_apply_apply, linearDualHomologyEquiv_homologyπ]

private lemma dualHomologyEquiv_homologyMap_bidualHom (i : ℤ)
    (x : K.homology i) (φ : (linearDual R K).homology (-i)) :
    linearDualHomologyEquiv (linearDual R K) (-i) i (neg_add_cancel i)
        (homologyMap (bidualHom K) i x) φ =
      i.negOnePow • linearDualHomologyEquiv K i (-i) (add_neg_cancel i) φ x := by
  obtain ⟨x, rfl⟩ := K.moduleCat_homologyπ_surjective i x
  obtain ⟨φ, rfl⟩ := (linearDual R K).moduleCat_homologyπ_surjective (-i) φ
  rw [moduleCat_homologyMap_homologyπ, linearDualHomologyEquiv_homologyπ,
    moduleCat_iCycles_cyclesMap_apply, linearDualXEquiv_bidualHom_f_apply,
    linearDualHomologyEquiv_homologyπ]

/-- Under the double Kronecker equivalence, the map on cohomology induced by the
chain-compatible bidual map is evaluation multiplied by `(-1)^i`. -/
@[simp]
theorem bidualHomologyEquiv_homologyMap_bidualHom (i : ℤ) (x : K.homology i) :
    bidualHomologyEquiv K i (homologyMap (bidualHom K) i x) =
      i.negOnePow • Module.Dual.eval R (K.homology i) x := by
  ext φ
  simp only [bidualHomologyEquiv, LinearEquiv.trans_apply, LinearEquiv.dualMap_apply,
    dualHomologyEquiv_homologyMap_bidualHom, LinearEquiv.apply_symm_apply,
    LinearMap.smul_apply, Module.Dual.eval_apply]

/-- The bidual map is a quasi-isomorphism in degree `i` exactly when the cohomology
module in that degree is reflexive. -/
theorem quasiIsoAt_bidualHom_iff (i : ℤ) :
    QuasiIsoAt (bidualHom K) i ↔ Module.IsReflexive R (K.homology i) := by
  rw [quasiIsoAt_iff_isIso_homologyMap, ConcreteCategory.isIso_iff_bijective]
  have h : ⇑(bidualHomologyEquiv K i) ∘ ⇑(homologyMap (bidualHom K) i) =
      (fun y ↦ i.negOnePow • y) ∘ ⇑(Module.Dual.eval R (K.homology i)) := by
    funext x
    exact bidualHomologyEquiv_homologyMap_bidualHom K i x
  rw [← (bidualHomologyEquiv K i).bijective.of_comp_iff', h,
    (MulAction.bijective i.negOnePow).of_comp_iff']
  exact ⟨fun h ↦ ⟨h⟩, fun h ↦ h.bijective_dual_eval'⟩

/-- Over self-injective commutative coefficients, the bidual map is a quasi-isomorphism
exactly when every cohomology module is reflexive. -/
theorem quasiIso_bidualHom_iff :
    QuasiIso (bidualHom K) ↔ ∀ i, Module.IsReflexive R (K.homology i) := by
  rw [quasiIso_iff]
  simp only [quasiIsoAt_bidualHom_iff]

/-- Over a self-injective commutative ring, a complex with reflexive cohomology is
quasi-isomorphic to its double dual through the signed evaluation map. -/
instance quasiIso_bidualHom [∀ i, Module.IsReflexive R (K.homology i)] :
    QuasiIso (bidualHom K) :=
  (quasiIso_bidualHom_iff K).2 inferInstance

end CochainComplex
