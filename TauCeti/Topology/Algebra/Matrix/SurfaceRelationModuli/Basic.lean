/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Homeomorph.Quotient
public import TauCeti.RepresentationTheory.SurfaceGroup.SpecialUnitary
public import TauCeti.Topology.Algebra.UnitaryGroup
import Mathlib.Topology.Algebra.MulAction
import TauCeti.GroupTheory.Commutator
import TauCeti.GroupTheory.GroupAction.ConjAct
import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Basic

/-!
# Twisted `SU(r)` surface commutator relation moduli

For natural numbers `r` and `g` and a complex scalar `ζ`, this file constructs and studies the
simultaneous-conjugation quotient `TauCeti.relationModuli r ζ g` of the twisted surface commutator
relation set `TauCeti.relationSet r ζ g`
(`TauCeti.RepresentationTheory.SurfaceGroup.SpecialUnitary`) inside `Fin g → SU(r) × SU(r)`
(`SU(r) = Matrix.specialUnitaryGroup (Fin r) ℂ`), cut out by

`⁅A₁, B₁⁆ * ⋯ * ⁅A_g, B_g⁆ = ζ • 1`

with Mathlib's group commutator convention `⁅A, B⁆ = A * B * A⁻¹ * B⁻¹`. Endowed with the quotient
topology, `TauCeti.relationModuli r ζ g` is compact and Hausdorff. When `ζ = exp (2πi d / r)`, the
primitive-root condition `IsPrimitiveRoot ζ r` expresses coprimality `gcd(r, d) = 1`; the quotient
is then the finite-dimensional holonomy model of the fixed-determinant central-curvature moduli
space on a closed oriented surface of genus `g`.

Genus-one existence, uniqueness up to conjugation, contractibility, simple connectivity, and
genus-one witnesses are established in
`TauCeti.Topology.Algebra.Matrix.SurfaceRelationModuli.GenusOne`.

## Main definitions

* `TauCeti.relationSubMulAction`: `relationSet r ζ g` as a `SubMulAction` of `ConjAct (SU(r))`.
* `TauCeti.relationModuli`: the quotient of `relationSet r ζ g` by simultaneous `SU(r)`-conjugation,
  with the quotient topology.
* `TauCeti.relationModuliMk`: the open quotient projection
  `relationSet r ζ g → relationModuli r ζ g`, invariant under `ConjAct (SU(r))`
  (`TauCeti.relationModuliMk_conjAct_smul`).
* `TauCeti.instMulActionQuotientCenterRelationSet`: the descended conjugation action of
  `SU(r) ⧸ Subgroup.center (SU(r))` on `relationSet r ζ g`, with homeomorphism
  `TauCeti.relationModuliHomeomorphQuotientCenter` identifying `relationModuli` with its orbit space
  (`TauCeti.relationModuliHomeomorphQuotientCenter_mk`).
* `TauCeti.instMulActionCenterTwistRelationSet` and
  `TauCeti.instMulActionCenterTwistRelationModuli`: the continuous entrywise central root-of-unity
  twist action of `Fin g → center(SU(r)) × center(SU(r))` on `relationSet` and its descent to
  `relationModuli`.

## Main results

* `TauCeti.isClosed_relationSet`, `TauCeti.isCompact_relationSet`,
  `TauCeti.instCompactSpaceRelationModuli`, `TauCeti.continuous_toConjAct_smul_relationSet`,
  `TauCeti.instT2SpaceRelationModuli`: `relationSet r ζ g` is closed and compact, simultaneous
  `SU(r)`-conjugation is jointly continuous, and `relationModuli r ζ g` is compact and Hausdorff.
* `TauCeti.toConjAct_smul_eq_self_iff_mem_center_of_mem_relationSet` and
  `TauCeti.isCancelSMul_quotientCenter_relationSet`: when `IsPrimitiveRoot ζ r`, every conjugation
  stabilizer on `relationSet r ζ g` equals `Subgroup.center (SU(r))` (by
  `TauCeti.relationSet_stabilizer_central`), so the descended action of
  `SU(r) ⧸ Subgroup.center (SU(r))` on `relationSet r ζ g` is free.
* `TauCeti.isEmpty_relationModuli_zero` and
  `TauCeti.isEmpty_relationModuli_zero_of_isPrimitiveRoot`: on the sphere (`g = 0`), the moduli is
  empty whenever `r ≠ 0` and `ζ ≠ 1`, in particular whenever `2 ≤ r` and `IsPrimitiveRoot ζ r`.
* `TauCeti.subsingleton_relationModuli_of_le_one` and
  `TauCeti.simplyConnectedSpace_relationModuli_of_le_one`: for `r ≤ 1` and `ζ = 1`,
  `relationModuli r 1 g` is a single point (hence simply connected) for every genus `g`.

## References

* M. F. Atiyah, R. Bott, *The Yang-Mills equations over Riemann surfaces*, Philos. Trans. Roy. Soc.
  London Ser. A **308** (1983), 523-615, §9.
* K. Wehrheim, C. T. Woodward, *Floer field theory for coprime rank and degree*, Geom. Topol.
  **20** (2016), 3135-3188, §3.3.
* A. Daemi, K. Fukaya, M. Lipyanskiy, *Lagrangians, SO(3)-instantons and the Atiyah-Floer
  conjecture*, arXiv:2109.07032, §2.
-/

public section

open Matrix Topology
open scoped commutatorElement

namespace TauCeti

/-! ### Simultaneous conjugation on `relationSet` and the moduli quotient -/

/-- Simultaneous conjugation by `ConjAct (SU(r))` preserves `relationSet r ζ g`: conjugation is a
group automorphism, and fixes the scalar matrix `ζ • 1`. -/
theorem conjAct_smul_mem_relationSet {r : ℕ} {ζ : ℂ} {g : ℕ}
    (u : ConjAct (Matrix.specialUnitaryGroup (Fin r) ℂ))
    {x : Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ}
    (hx : x ∈ relationSet r ζ g) :
    u • x ∈ relationSet r ζ g := by
  rw [mem_relationSet] at hx ⊢
  let v := ConjAct.ofConjAct u
  let φ : Matrix.specialUnitaryGroup (Fin r) ℂ →* Matrix.specialUnitaryGroup (Fin r) ℂ :=
    (MulAut.conj v).toMonoidHom
  have hlist : (List.ofFn fun j => ⁅((u • x) j).1, ((u • x) j).2⁆) =
      (List.ofFn fun j => ⁅(x j).1, (x j).2⁆).map φ := by
    rw [List.map_ofFn]
    refine congrArg List.ofFn (funext fun j => ?_)
    simp only [Function.comp_def, Pi.smul_apply, Prod.smul_fst, Prod.smul_snd,
      ConjAct.smul_eq_mulAut_conj, φ, v, MulEquiv.coe_toMonoidHom, map_commutatorElement]
  rw [hlist, ← map_list_prod]
  simp only [φ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Submonoid.coe_mul, hx,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.specialUnitaryGroup.coe_mul_coe_inv]

/-- `relationSet r ζ g` as an invariant subset (`SubMulAction`) under simultaneous conjugation by
`ConjAct (SU(r))`. -/
def relationSubMulAction (r : ℕ) (ζ : ℂ) (g : ℕ) :
    SubMulAction (ConjAct (Matrix.specialUnitaryGroup (Fin r) ℂ))
      (Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ) where
  carrier := relationSet r ζ g
  smul_mem' u _ hx := conjAct_smul_mem_relationSet u hx

/-- Membership in `relationSubMulAction r ζ g` coincides with membership in `relationSet r ζ g`. -/
@[simp]
theorem mem_relationSubMulAction_iff {r : ℕ} {ζ : ℂ} {g : ℕ}
    {x : Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ} :
    x ∈ relationSubMulAction r ζ g ↔ x ∈ relationSet r ζ g :=
  (Iff.rfl)

/-- Simultaneous conjugation action of `ConjAct (SU(r))` directly on `relationSet r ζ g`. -/
instance instMulActionConjActRelationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    MulAction (ConjAct (Matrix.specialUnitaryGroup (Fin r) ℂ)) (relationSet r ζ g) :=
  inferInstanceAs (MulAction (ConjAct (Matrix.specialUnitaryGroup (Fin r) ℂ))
    (relationSubMulAction r ζ g))

/-- Coercing `u • x` from `relationSet r ζ g` to the ambient tuple type agrees with `u • x.val`. -/
@[simp]
theorem relationSet.val_conjAct_smul {r : ℕ} {ζ : ℂ} {g : ℕ}
    (u : ConjAct (Matrix.specialUnitaryGroup (Fin r) ℂ)) (x : relationSet r ζ g) :
    ((u • x : relationSet r ζ g) :
      Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ) =
      u • x.val :=
  (rfl)

/-- Each element of `ConjAct (SU(r))` acts continuously on `relationSet r ζ g`. -/
instance instContinuousConstSMulConjActRelationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    ContinuousConstSMul (ConjAct (Matrix.specialUnitaryGroup (Fin r) ℂ))
      (relationSet r ζ g) :=
  inferInstanceAs (ContinuousConstSMul (ConjAct (Matrix.specialUnitaryGroup (Fin r) ℂ))
    (relationSubMulAction r ζ g))

/-- The conjugation moduli `R_g / SU(r)` of the twisted `SU(r)` surface relation: the orbit
quotient of `relationSet r ζ g` under simultaneous conjugation by `ConjAct (SU(r))`, endowed with
the quotient topology. -/
abbrev relationModuli (r : ℕ) (ζ : ℂ) (g : ℕ) : Type :=
  MulAction.orbitRel.Quotient (ConjAct (Matrix.specialUnitaryGroup (Fin r) ℂ))
    (relationSet r ζ g)

/-- The quotient projection from `relationSet r ζ g` onto `relationModuli r ζ g`. -/
def relationModuliMk {r : ℕ} {ζ : ℂ} {g : ℕ} (x : relationSet r ζ g) :
    relationModuli r ζ g :=
  Quotient.mk _ x

/-- The quotient projection `relationModuliMk` is surjective. -/
theorem relationModuliMk_surjective (r : ℕ) (ζ : ℂ) (g : ℕ) :
    Function.Surjective (@relationModuliMk r ζ g) :=
  Quotient.mk_surjective

/-- The quotient projection `relationModuliMk` is continuous. -/
theorem continuous_relationModuliMk (r : ℕ) (ζ : ℂ) (g : ℕ) :
    Continuous (@relationModuliMk r ζ g) :=
  continuous_quot_mk

/-- The quotient projection `relationModuliMk` is a topological quotient map. -/
theorem isQuotientMap_relationModuliMk (r : ℕ) (ζ : ℂ) (g : ℕ) :
    IsQuotientMap (@relationModuliMk r ζ g) :=
  isQuotientMap_quot_mk

/-- Two points of `relationSet r ζ g` represent the same class in `relationModuli r ζ g` precisely
when one is carried to the other by simultaneous conjugation by an element of `SU(r)`. -/
@[simp]
theorem relationModuliMk_eq_iff {r : ℕ} {ζ : ℂ} {g : ℕ} (x y : relationSet r ζ g) :
    relationModuliMk x = relationModuliMk y ↔
      ∃ u : Matrix.specialUnitaryGroup (Fin r) ℂ, ConjAct.toConjAct u • y.val = x.val := by
  rw [relationModuliMk, relationModuliMk, Quotient.eq, MulAction.orbitRel_apply,
    MulAction.mem_orbit_iff]
  simp_rw [Subtype.ext_iff, relationSet.val_conjAct_smul]
  exact ConjAct.toConjAct.toEquiv.exists_congr_left

/-- Simultaneous conjugation by `ConjAct (SU(r))` acts trivially on `relationModuli r ζ g`. -/
@[simp]
theorem relationModuliMk_conjAct_smul {r : ℕ} {ζ : ℂ} {g : ℕ}
    (u : ConjAct (Matrix.specialUnitaryGroup (Fin r) ℂ)) (x : relationSet r ζ g) :
    relationModuliMk (u • x) = relationModuliMk x :=
  MulAction.orbitRel.Quotient.quotient_smul_eq

/-- The quotient projection `relationModuliMk` is an open quotient map, since `ConjAct (SU(r))`
acts by homeomorphisms on `relationSet r ζ g`. -/
theorem isOpenQuotientMap_relationModuliMk (r : ℕ) (ζ : ℂ) (g : ℕ) :
    IsOpenQuotientMap (@relationModuliMk r ζ g) :=
  MulAction.isOpenQuotientMap_quotientMk

/-! ### Compactness and Hausdorffness -/

/-- Continuity of the ordered commutator-product map from `Fin g → SU(r) × SU(r)` into
`Matrix (Fin r) (Fin r) ℂ`. -/
private theorem continuous_commutatorProd (r g : ℕ) :
    Continuous (fun x : Fin g →
        Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ =>
      ((List.ofFn fun j => ⁅(x j).1, (x j).2⁆).prod : Matrix (Fin r) (Fin r) ℂ)) := by
  refine continuous_subtypeVal.comp ?_
  simp only [List.ofFn_eq_map]
  refine continuous_list_prod (List.finRange g) fun j _ => ?_
  simp only [commutatorElement_def]
  fun_prop

/-- `relationSet r ζ g` is a closed subset of `Fin g → SU(r) × SU(r)`. -/
theorem isClosed_relationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    IsClosed (relationSet r ζ g) := by
  have h : relationSet r ζ g =
      (fun x : Fin g →
          Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ =>
        ((List.ofFn fun j => ⁅(x j).1, (x j).2⁆).prod : Matrix (Fin r) (Fin r) ℂ)) ⁻¹'
      {ζ • 1} :=
    Set.ext fun _ => mem_relationSet
  rw [h]
  exact isClosed_singleton.preimage (continuous_commutatorProd r g)

/-- `relationSet r ζ g` is a compact subset of `Fin g → SU(r) × SU(r)`: it is closed in a finite
product of copies of the compact group `SU(r)`. -/
theorem isCompact_relationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    IsCompact (relationSet r ζ g) :=
  IsCompact.of_isClosed_subset isCompact_univ (isClosed_relationSet r ζ g) (Set.subset_univ _)

/-- `relationSet r ζ g` is a compact topological space. -/
instance instCompactSpaceRelationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    CompactSpace (relationSet r ζ g) :=
  isCompact_iff_compactSpace.mp (isCompact_relationSet r ζ g)

/-- `relationModuli r ζ g` is compact, as a quotient of the compact space `relationSet r ζ g`. -/
instance instCompactSpaceRelationModuli (r : ℕ) (ζ : ℂ) (g : ℕ) :
    CompactSpace (relationModuli r ζ g) :=
  Quotient.compactSpace

/-- Joint continuity of simultaneous `SU(r)`-conjugation `(u, x) ↦ ConjAct.toConjAct u • x` on
`SU(r) × relationSet r ζ g`. -/
theorem continuous_toConjAct_smul_relationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    Continuous (fun p : Matrix.specialUnitaryGroup (Fin r) ℂ × relationSet r ζ g =>
      ConjAct.toConjAct p.1 • p.2) := by
  refine continuous_induced_rng.2 ?_
  have hact : Continuous fun p : Matrix.specialUnitaryGroup (Fin r) ℂ ×
      (Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ) =>
      ConjAct.toConjAct p.1 • p.2 :=
    continuous_pi fun j => by
      simp only [Pi.smul_apply, Prod.smul_def, ConjAct.toConjAct_smul]
      fun_prop
  simpa only [Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq,
    relationSet.val_conjAct_smul] using
    hact.comp (continuous_id.prodMap continuous_subtypeVal)

/-- `relationModuli r ζ g` is Hausdorff: `relationModuliMk` is an open quotient map and the orbit
relation is the image of the compact space `SU(r) × relationSet r ζ g`, hence closed. -/
instance instT2SpaceRelationModuli (r : ℕ) (ζ : ℂ) (g : ℕ) :
    T2Space (relationModuli r ζ g) := by
  rw [t2Space_iff_of_isOpenQuotientMap (isOpenQuotientMap_relationModuliMk r ζ g)]
  let Φ : Matrix.specialUnitaryGroup (Fin r) ℂ × relationSet r ζ g →
      relationSet r ζ g × relationSet r ζ g :=
    fun p => (ConjAct.toConjAct p.1 • p.2, p.2)
  have hcont : Continuous Φ :=
    (continuous_toConjAct_smul_relationSet r ζ g).prodMk continuous_snd
  have hrange : {q : relationSet r ζ g × relationSet r ζ g |
      relationModuliMk q.1 = relationModuliMk q.2} = Set.range Φ := by
    ext ⟨a, b⟩
    simp only [Set.mem_ofPred_eq, relationModuliMk_eq_iff, Set.mem_range, Prod.ext_iff, Φ]
    refine ⟨fun ⟨u, hu⟩ => ⟨(u, b), Subtype.ext hu, rfl⟩,
      fun ⟨⟨u, b'⟩, ha, hb⟩ => ?_⟩
    subst hb
    exact ⟨u, congrArg Subtype.val ha⟩
  rw [hrange]
  exact (isCompact_range hcont).isClosed

/-! ### Exact conjugation stabilizers and the free `PSU(r)` action -/

/-- **Exact conjugation stabilizers on `relationSet`.** When `IsPrimitiveRoot ζ r`, an element of
`SU(r)` fixes `x ∈ relationSet r ζ g` under simultaneous conjugation if and only if it lies in the
center of `SU(r)`. -/
theorem toConjAct_smul_eq_self_iff_mem_center_of_mem_relationSet {r : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ r) {g : ℕ}
    {x : Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ}
    (hx : x ∈ relationSet r ζ g) (u : Matrix.specialUnitaryGroup (Fin r) ℂ) :
    ConjAct.toConjAct u • x = x ↔
      u ∈ Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) := by
  refine ⟨fun h => relationSet_stabilizer_central hζ hx fun j => ?_,
    fun hu => ConjAct.toConjAct_smul_pi_prod_eq_self_of_mem_center hu x⟩
  rw [commute_iff_eq, commute_iff_eq]
  simpa only [mul_inv_eq_iff_eq_mul] using
    ConjAct.toConjAct_smul_pi_prod_eq_iff.mp h j

/-- Simultaneous conjugation by `SU(r)` descends to an action of the projective quotient
`SU(r) ⧸ Subgroup.center (SU(r))` on `relationSet r ζ g`. -/
noncomputable instance instMulActionQuotientCenterRelationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    MulAction (Matrix.specialUnitaryGroup (Fin r) ℂ ⧸
      Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ)) (relationSet r ζ g) :=
  let φ : Matrix.specialUnitaryGroup (Fin r) ℂ →* Equiv.Perm (relationSet r ζ g) :=
    (MulAction.toPermHom (ConjAct (Matrix.specialUnitaryGroup (Fin r) ℂ))
      (relationSet r ζ g)).comp ConjAct.toConjAct.toMonoidHom
  MulAction.compHom (relationSet r ζ g) <|
    QuotientGroup.lift (Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ)) φ fun u hu => by
      ext x : 2
      simp only [φ, MonoidHom.comp_apply, MulAction.toPermHom_apply, MulAction.toPerm_apply,
        MulEquiv.coe_toMonoidHom, Equiv.Perm.coe_one, id_eq, relationSet.val_conjAct_smul]
      exact ConjAct.toConjAct_smul_pi_prod_eq_self_of_mem_center hu x.val

/-- A coset `QuotientGroup.mk u` in `SU(r) ⧸ center(SU(r))` acts on `relationSet r ζ g` by
simultaneous conjugation by `u`. -/
@[simp]
theorem relationSet.val_quotientCenter_mk_smul {r : ℕ} {ζ : ℂ} {g : ℕ}
    (u : Matrix.specialUnitaryGroup (Fin r) ℂ) (x : relationSet r ζ g) :
    (((QuotientGroup.mk u : Matrix.specialUnitaryGroup (Fin r) ℂ ⧸
        Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ)) • x : relationSet r ζ g) :
      Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ) =
      ConjAct.toConjAct u • x.val :=
  (rfl)

/-- **Freeness of the effective `PSU(r)` action on `relationSet`.** When `IsPrimitiveRoot ζ r`, the
descended action of `SU(r) ⧸ Subgroup.center (SU(r))` on `relationSet r ζ g` is cancellative
(free). -/
theorem isCancelSMul_quotientCenter_relationSet {r : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ r)
    (g : ℕ) :
    IsCancelSMul (Matrix.specialUnitaryGroup (Fin r) ℂ ⧸
      Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ)) (relationSet r ζ g) where
  right_cancel' q₁ q₂ x h := by
    obtain ⟨u₁, rfl⟩ := QuotientGroup.mk_surjective q₁
    obtain ⟨u₂, rfl⟩ := QuotientGroup.mk_surjective q₂
    apply QuotientGroup.eq.mpr
    have hfix : ConjAct.toConjAct (u₁⁻¹ * u₂) • x.val = x.val := by
      rw [map_mul, mul_smul, map_inv, inv_smul_eq_iff]
      simpa only [relationSet.val_quotientCenter_mk_smul] using (congrArg Subtype.val h).symm
    exact (toConjAct_smul_eq_self_iff_mem_center_of_mem_relationSet hζ x.property
      (u₁⁻¹ * u₂)).mp hfix

/-- Homeomorphism identifying `relationModuli r ζ g` with the orbit quotient of the effective
`SU(r) ⧸ Subgroup.center (SU(r))` action on `relationSet r ζ g`. -/
noncomputable def relationModuliHomeomorphQuotientCenter (r : ℕ) (ζ : ℂ) (g : ℕ) :
    relationModuli r ζ g ≃ₜ
      MulAction.orbitRel.Quotient
        (Matrix.specialUnitaryGroup (Fin r) ℂ ⧸
          Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ))
        (relationSet r ζ g) :=
  Homeomorph.Quotient.congrRight fun x y => by
    simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff,
      QuotientGroup.mk_surjective.exists, Subtype.ext_iff, relationSet.val_conjAct_smul,
      relationSet.val_quotientCenter_mk_smul]
    exact ConjAct.toConjAct.toEquiv.exists_congr_left

/-- `relationModuliHomeomorphQuotientCenter` sends `relationModuliMk x` to `Quotient.mk _ x`. -/
@[simp]
theorem relationModuliHomeomorphQuotientCenter_mk {r : ℕ} {ζ : ℂ} {g : ℕ}
    (x : relationSet r ζ g) :
    relationModuliHomeomorphQuotientCenter r ζ g (relationModuliMk x) = Quotient.mk _ x :=
  (rfl)

/-! ### Sphere emptiness, low rank, and central holonomy twists -/

/-- On the sphere (`g = 0`), `relationModuli r ζ 0` is empty whenever `r ≠ 0` and `ζ ≠ 1`. -/
theorem isEmpty_relationModuli_zero {r : ℕ} (hr : r ≠ 0) {ζ : ℂ} (hζ : ζ ≠ 1) :
    IsEmpty (relationModuli r ζ 0) :=
  ⟨fun q => (isEmpty_relationSet_zero hr hζ).false q.out⟩

/-- On the sphere (`g = 0`), `relationModuli r ζ 0` is empty whenever `2 ≤ r` and
`IsPrimitiveRoot ζ r`. -/
theorem isEmpty_relationModuli_zero_of_isPrimitiveRoot {r : ℕ} (hr : 2 ≤ r) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ r) :
    IsEmpty (relationModuli r ζ 0) :=
  isEmpty_relationModuli_zero (by omega) (hζ.ne_one hr)

/-- For `r ≤ 1`, `SU(r)` is a subsingleton, so `relationModuli r ζ g` is a subsingleton for every
`ζ` and every genus `g`. -/
theorem subsingleton_relationModuli_of_le_one {r : ℕ} (hr : r ≤ 1) (ζ : ℂ) (g : ℕ) :
    Subsingleton (relationModuli r ζ g) := by
  have : Subsingleton (Fin r) := ⟨fun a b => Fin.ext (by omega)⟩
  infer_instance

/-- At `ζ = 1`, `relationModuli r 1 g` is nonempty for all `r` and `g`. -/
instance instNonemptyRelationModuliUntwisted (r g : ℕ) :
    Nonempty (relationModuli r 1 g) :=
  ⟨relationModuliMk (Classical.arbitrary (relationSet r 1 g))⟩

/-- For `r ≤ 1`, `relationModuli r 1 g` is simply connected for every genus `g`. -/
theorem simplyConnectedSpace_relationModuli_of_le_one {r : ℕ} (hr : r ≤ 1) (g : ℕ) :
    SimplyConnectedSpace (relationModuli r 1 g) := by
  have : Subsingleton (relationModuli r 1 g) := subsingleton_relationModuli_of_le_one hr 1 g
  infer_instance

/-- Entrywise multiplication by pairs of central elements of `SU(r)` preserves `relationSet r ζ g`:
central scalars cancel in every commutator `⁅c₁ * A, c₂ * B⁆ = ⁅A, B⁆`. -/
theorem centerTwist_mem_relationSet {r : ℕ} {ζ : ℂ} {g : ℕ}
    (ε : Fin g → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
      Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ))
    {x : Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ}
    (hx : x ∈ relationSet r ζ g) :
    (fun j => (((ε j).1 : Matrix.specialUnitaryGroup (Fin r) ℂ) * (x j).1,
      ((ε j).2 : Matrix.specialUnitaryGroup (Fin r) ℂ) * (x j).2)) ∈ relationSet r ζ g := by
  rw [mem_relationSet] at hx ⊢
  have hcomm_eq : ∀ j : Fin g,
      ⁅((ε j).1 : Matrix.specialUnitaryGroup (Fin r) ℂ) * (x j).1,
        ((ε j).2 : Matrix.specialUnitaryGroup (Fin r) ℂ) * (x j).2⁆ =
      ⁅(x j).1, (x j).2⁆ := fun j => by
    rw [← Subgroup.mem_center_iff.mp (ε j).1.property (x j).1,
      ← Subgroup.mem_center_iff.mp (ε j).2.property (x j).2]
    exact commutatorElement_mul_mul_of_mem_center (ε j).1.property (ε j).2.property
  simpa only [hcomm_eq] using hx

/-- Scalar multiplication of central holonomy twists `Fin g → center(SU(r)) × center(SU(r))` on
`relationSet r ζ g` by entrywise multiplication. -/
noncomputable instance instSMulCenterTwistRelationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    SMul (Fin g → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
      Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ)) (relationSet r ζ g) where
  smul ε x := ⟨fun j => (((ε j).1 : Matrix.specialUnitaryGroup (Fin r) ℂ) * (x.val j).1,
      ((ε j).2 : Matrix.specialUnitaryGroup (Fin r) ℂ) * (x.val j).2),
    centerTwist_mem_relationSet ε x.property⟩

/-- Coercing a central twist `ε • x` from `relationSet r ζ g` multiplies each pair `(A_j, B_j)`
entrywise by `((ε j).1, (ε j).2)`. -/
@[simp]
theorem relationSet.val_centerTwist_smul {r : ℕ} {ζ : ℂ} {g : ℕ}
    (ε : Fin g → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
      Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ)) (x : relationSet r ζ g) :
    ((ε • x : relationSet r ζ g) :
      Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ) =
      fun j => (((ε j).1 : Matrix.specialUnitaryGroup (Fin r) ℂ) * (x.val j).1,
        ((ε j).2 : Matrix.specialUnitaryGroup (Fin r) ℂ) * (x.val j).2) :=
  (rfl)

/-- The group `Fin g → center(SU(r)) × center(SU(r))` of central holonomy twists acts on
`relationSet r ζ g` by entrywise multiplication. -/
noncomputable instance instMulActionCenterTwistRelationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    MulAction (Fin g → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
      Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ)) (relationSet r ζ g) where
  one_smul x := Subtype.ext <| by simp [relationSet.val_centerTwist_smul]
  mul_smul ε₁ ε₂ x := Subtype.ext <| by simp [relationSet.val_centerTwist_smul, mul_assoc]

/-- The central holonomy twist action on `relationSet r ζ g` is jointly continuous. -/
instance instContinuousSMulCenterTwistRelationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    ContinuousSMul (Fin g → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
      Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ)) (relationSet r ζ g) where
  continuous_smul := continuous_induced_rng.2 <| by
    simp only [Function.comp_def, relationSet.val_centerTwist_smul]
    have hact : Continuous fun p : (Fin g →
        Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
        Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ)) ×
        (Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ) =>
        fun j => (((p.1 j).1 : Matrix.specialUnitaryGroup (Fin r) ℂ) * (p.2 j).1,
          ((p.1 j).2 : Matrix.specialUnitaryGroup (Fin r) ℂ) * (p.2 j).2) :=
      continuous_pi fun j => by fun_prop
    exact hact.comp (continuous_id.prodMap continuous_subtypeVal)

/-- Entrywise central twisting commutes with simultaneous `SU(r)`-conjugation, so it descends to a
group action on `relationModuli r ζ g`. -/
noncomputable instance instMulActionCenterTwistRelationModuli (r : ℕ) (ζ : ℂ) (g : ℕ) :
    MulAction (Fin g → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
      Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ)) (relationModuli r ζ g) where
  smul ε := Quotient.map' (ε • ·) fun x y ⟨u, hu⟩ => ⟨u, Subtype.ext <| by
    obtain ⟨u, rfl⟩ := ConjAct.toConjAct.surjective u
    have hu' := ConjAct.toConjAct_smul_pi_prod_eq_iff.mp (congrArg Subtype.val hu)
    rw [relationSet.val_conjAct_smul, relationSet.val_centerTwist_smul,
      relationSet.val_centerTwist_smul, ConjAct.toConjAct_smul_pi_prod_eq_iff]
    exact fun j =>
      ⟨by simpa only [← ConjAct.toConjAct_smul,
          ConjAct.smul_mul_of_mem_center _ (ε j).1.property] using
          congrArg (((ε j).1 : Matrix.specialUnitaryGroup (Fin r) ℂ) * ·) (hu' j).1,
        by simpa only [← ConjAct.toConjAct_smul,
          ConjAct.smul_mul_of_mem_center _ (ε j).2.property] using
          congrArg (((ε j).2 : Matrix.specialUnitaryGroup (Fin r) ℂ) * ·) (hu' j).2⟩⟩
  one_smul q := Quotient.inductionOn' q fun x => congrArg Quotient.mk'' (one_smul _ x)
  mul_smul ε₁ ε₂ q :=
    Quotient.inductionOn' q fun x => congrArg Quotient.mk'' (mul_smul ε₁ ε₂ x)

/-- The quotient projection `relationModuliMk` is equivariant for central holonomy twists. -/
@[simp]
theorem centerTwist_smul_relationModuliMk {r : ℕ} {ζ : ℂ} {g : ℕ}
    (ε : Fin g → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
      Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ)) (x : relationSet r ζ g) :
    ε • relationModuliMk x = relationModuliMk (ε • x) :=
  (rfl)

/-- The descended central holonomy twist action on `relationModuli r ζ g` is jointly continuous. -/
instance instContinuousSMulCenterTwistRelationModuli (r : ℕ) (ζ : ℂ) (g : ℕ) :
    ContinuousSMul (Fin g → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
      Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ)) (relationModuli r ζ g) where
  continuous_smul := by
    have hq : IsQuotientMap (Prod.map
        (id : (Fin g → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
          Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ)) → _)
        (@relationModuliMk r ζ g)) :=
      (IsOpenQuotientMap.id.prodMap (isOpenQuotientMap_relationModuliMk r ζ g)).isQuotientMap
    rw [hq.continuous_iff]
    have hcomp : (fun p => p.1 • p.2) ∘ Prod.map
          (id : (Fin g → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
            Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ)) → _)
          (@relationModuliMk r ζ g) =
        (@relationModuliMk r ζ g) ∘ (fun p => p.1 • p.2) :=
      funext fun ⟨ε, x⟩ => centerTwist_smul_relationModuliMk ε x
    rw [hcomp]
    exact (continuous_relationModuliMk r ζ g).comp continuous_smul

end TauCeti
