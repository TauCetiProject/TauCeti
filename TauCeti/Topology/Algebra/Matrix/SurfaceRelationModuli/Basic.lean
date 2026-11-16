/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Homeomorph.Quotient
public import TauCeti.Analysis.Matrix.UnitaryGroup.SpecialUnitary
public import TauCeti.Topology.Algebra.UnitaryGroup
import TauCeti.LinearAlgebra.Matrix.Diagonal

/-!
# Twisted `SU(r)` surface commutator relation moduli

For natural numbers `r` and `g` and a complex scalar `ζ`, this file defines and studies the twisted
surface commutator relation set `TauCeti.SpecialUnitary.relationSet r ζ g` inside
`Fin g → SU(r) × SU(r)` (`SU(r) = Matrix.specialUnitaryGroup (Fin r) ℂ`), cut out by the equation

`⁅A₁, B₁⁆ * ⋯ * ⁅A_g, B_g⁆ = ζ • 1`

with Mathlib's group commutator convention `⁅A, B⁆ = A * B * A⁻¹ * B⁻¹`, together with its quotient
`TauCeti.SpecialUnitary.relationModuli r ζ g` by simultaneous `SU(r)`-conjugation carrying the
quotient topology. When `ζ = exp (2πi d / r)`, the primitive-root condition `IsPrimitiveRoot ζ r`
expresses coprimality `gcd(r, d) = 1`; the quotient is then the finite-dimensional holonomy model
of the fixed-determinant central-curvature moduli space on a closed oriented surface of genus `g`.

Genus-one existence, uniqueness up to conjugation, simple connectivity, and genus-one witnesses are
established in `TauCeti.Topology.Algebra.Matrix.SurfaceRelationModuli.GenusOne`.

## Main definitions

* `TauCeti.SpecialUnitary.relationSet`: tuples `(A₁, B₁, …, A_g, B_g)` in `SU(r)` whose ordered
  product of group commutators equals `ζ • 1`.
* `TauCeti.SpecialUnitary.relationSubMulAction`: `relationSet r ζ g` as a `SubMulAction` of
  `ConjAct (SU(r))`.
* `TauCeti.SpecialUnitary.relationModuli`: the quotient of `relationSet r ζ g` by simultaneous
  `SU(r)`-conjugation, with the quotient topology.
* `TauCeti.SpecialUnitary.relationModuliMk`: the open quotient projection
  `relationSet r ζ g → relationModuli r ζ g`.
* `TauCeti.SpecialUnitary.instMulActionQuotientCenterRelationSet`: the descended conjugation action
  of `SU(r) ⧸ Subgroup.center (SU(r))` on `relationSet r ζ g`, with homeomorphism
  `TauCeti.SpecialUnitary.relationModuliHomeomorphQuotientCenter` identifying `relationModuli` with
  its orbit space.
* `TauCeti.SpecialUnitary.instMulActionCenterTwistRelationSet` and
  `TauCeti.SpecialUnitary.instMulActionCenterTwistRelationModuli`: the continuous entrywise central
  root-of-unity twist action of `Fin g → center(SU(r)) × center(SU(r))` on `relationSet` and its
  descent to `relationModuli`.

## Main results

* `TauCeti.SpecialUnitary.isClosed_relationSet`, `TauCeti.SpecialUnitary.isCompact_relationSet`,
  `TauCeti.SpecialUnitary.instCompactSpaceRelationModuli`,
  `TauCeti.SpecialUnitary.instT2SpaceRelationModuli`: `relationSet r ζ g` is closed and compact, and
  `relationModuli r ζ g` is compact and Hausdorff.
* `TauCeti.SpecialUnitary.relationSet_stabilizer_central`: when `IsPrimitiveRoot ζ r`, every
  `u ∈ SU(r)` commuting with all entries of a point of `relationSet r ζ g` lies in the center of
  `SU(r)`; equivalently (`TauCeti.SpecialUnitary.conjAct_toConjAct_smul_eq_self_iff_mem_center`)
  every conjugation stabilizer equals `Subgroup.center (SU(r))`, and the descended action of
  `SU(r) ⧸ Subgroup.center (SU(r))` on `relationSet r ζ g` is free
  (`TauCeti.SpecialUnitary.isCancelSMul_quotientCenter_relationSet`).
* `TauCeti.SpecialUnitary.isEmpty_relationModuli_zero` and
  `TauCeti.SpecialUnitary.isEmpty_relationModuli_zero_of_isPrimitiveRoot`: on the sphere (`g = 0`),
  the moduli is empty whenever `1 ≤ r` and `ζ ≠ 1`, in particular whenever `2 ≤ r` and
  `IsPrimitiveRoot ζ r`.
* `TauCeti.SpecialUnitary.subsingleton_relationModuli_of_le_one` and
  `TauCeti.SpecialUnitary.simplyConnectedSpace_relationModuli_of_le_one`: for `r ≤ 1` and `ζ = 1`,
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

namespace TauCeti.SpecialUnitary

/-! ### The twisted commutator relation set and conjugation quotient -/

/-- The twisted surface commutator relation set in `SU(r)`: tuples `(A₁, B₁, …, A_g, B_g)` in
`Matrix.specialUnitaryGroup (Fin r) ℂ` whose ordered product of group commutators
`⁅A₁, B₁⁆ * ⋯ * ⁅A_g, B_g⁆` equals the scalar matrix `ζ • 1`. -/
def relationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    Set (Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ) :=
  {x | ((List.ofFn fun j => ⁅(x j).1, (x j).2⁆).prod : Matrix (Fin r) (Fin r) ℂ) = ζ • 1}

/-- Membership in `relationSet r ζ g` is equality of the ordered commutator product with `ζ • 1`. -/
@[simp]
theorem mem_relationSet_iff {r : ℕ} {ζ : ℂ} {g : ℕ}
    {x : Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ} :
    x ∈ relationSet r ζ g ↔
      ((List.ofFn fun j => ⁅(x j).1, (x j).2⁆).prod : Matrix (Fin r) (Fin r) ℂ) = ζ • 1 :=
  (Iff.rfl)

/-- At genus `0`, membership in `relationSet r ζ 0` reduces to `1 = ζ • 1` in
`Matrix (Fin r) (Fin r) ℂ`. -/
theorem mem_relationSet_zero_iff {r : ℕ} {ζ : ℂ}
    {x : Fin 0 → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ} :
    x ∈ relationSet r ζ 0 ↔ (1 : Matrix (Fin r) (Fin r) ℂ) = ζ • 1 := by
  simp [mem_relationSet_iff]

/-- At genus `1`, membership in `relationSet r ζ 1` is the single commutator equation
`⁅(x 0).1, (x 0).2⁆ = ζ • 1`. -/
theorem mem_relationSet_one_iff {r : ℕ} {ζ : ℂ}
    {x : Fin 1 → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ} :
    x ∈ relationSet r ζ 1 ↔
      (↑⁅(x 0).1, (x 0).2⁆ : Matrix (Fin r) (Fin r) ℂ) = ζ • 1 := by
  simp [mem_relationSet_iff, List.ofFn_succ]

/-- Simultaneous conjugation by `ConjAct (SU(r))` preserves `relationSet r ζ g`: conjugation is a
group automorphism, and fixes the scalar matrix `ζ • 1`. -/
theorem conjAct_smul_mem_relationSet {r : ℕ} {ζ : ℂ} {g : ℕ}
    (u : ConjAct (Matrix.specialUnitaryGroup (Fin r) ℂ))
    {x : Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ}
    (hx : x ∈ relationSet r ζ g) :
    u • x ∈ relationSet r ζ g := by
  rw [mem_relationSet_iff] at hx ⊢
  let v := ConjAct.ofConjAct u
  let φ : Matrix.specialUnitaryGroup (Fin r) ℂ →* Matrix.specialUnitaryGroup (Fin r) ℂ :=
    (MulAut.conj v).toMonoidHom
  have hlist : (List.ofFn fun j => ⁅((u • x) j).1, ((u • x) j).2⁆) =
      (List.ofFn fun j => ⁅(x j).1, (x j).2⁆).map φ := by
    rw [List.map_ofFn]
    exact congrArg List.ofFn (funext fun j => (map_commutatorElement φ (x j).1 (x j).2).symm)
  have hφ : ∀ a, φ a = v * a * v⁻¹ := fun _ => rfl
  rw [hlist, ← map_list_prod, hφ, Submonoid.coe_mul, Submonoid.coe_mul, hx, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, ← Submonoid.coe_mul, mul_inv_cancel, OneMemClass.coe_one]

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
noncomputable instance instMulActionConjActRelationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    MulAction (ConjAct (Matrix.specialUnitaryGroup (Fin r) ℂ)) (relationSet r ζ g) where
  smul u x := ⟨u • x.1, conjAct_smul_mem_relationSet u x.2⟩
  one_smul x := Subtype.ext (one_smul _ x.1)
  mul_smul u v x := Subtype.ext (mul_smul u v x.1)

/-- Coercing `u • x` from `relationSet r ζ g` to the ambient tuple type agrees with `u • x.1`. -/
@[simp]
theorem conjAct_smul_relationSet_coe {r : ℕ} {ζ : ℂ} {g : ℕ}
    (u : ConjAct (Matrix.specialUnitaryGroup (Fin r) ℂ)) (x : relationSet r ζ g) :
    ((u • x : relationSet r ζ g) :
      Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ) =
      u • x.1 :=
  (rfl)

/-- Each element of `ConjAct (SU(r))` acts continuously on `relationSet r ζ g`. -/
instance instContinuousConstSMulConjActRelationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    ContinuousConstSMul (ConjAct (Matrix.specialUnitaryGroup (Fin r) ℂ))
      (relationSet r ζ g) where
  continuous_const_smul _ := by
    refine Continuous.subtype_mk (continuous_pi fun j => ?_) _
    have hj : Continuous fun x : relationSet r ζ g => x.1 j :=
      (continuous_apply j).comp continuous_subtype_val
    exact Continuous.prodMk
      ((continuous_const.mul (continuous_fst.comp hj)).mul continuous_const)
      ((continuous_const.mul (continuous_snd.comp hj)).mul continuous_const)

/-- The conjugation moduli `R_g / SU(r)` of the twisted `SU(r)` surface relation: the quotient of
`relationSet r ζ g` by the pullback of the simultaneous conjugation orbit relation, endowed with
the quotient topology. -/
abbrev relationModuli (r : ℕ) (ζ : ℂ) (g : ℕ) : Type :=
  Quotient ((MulAction.orbitRel (ConjAct (Matrix.specialUnitaryGroup (Fin r) ℂ))
    (Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ)).comap
    (Subtype.val : relationSet r ζ g → _))

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
      ∃ u : Matrix.specialUnitaryGroup (Fin r) ℂ, ConjAct.toConjAct u • y.1 = x.1 := by
  rw [relationModuliMk, relationModuliMk, Quotient.eq, Setoid.comap_rel,
    MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  exact ConjAct.toConjAct.toEquiv.exists_congr_left

/-- Homeomorphism identifying `relationModuli r ζ g` with the `MulAction.orbitRel.Quotient` of
`ConjAct (SU(r))` acting directly on `relationSet r ζ g`. -/
noncomputable def relationModuliHomeomorphOrbitQuotient (r : ℕ) (ζ : ℂ) (g : ℕ) :
    relationModuli r ζ g ≃ₜ
      MulAction.orbitRel.Quotient (ConjAct (Matrix.specialUnitaryGroup (Fin r) ℂ))
        (relationSet r ζ g) :=
  Homeomorph.Quotient.congrRight fun x y => by
    simp only [Setoid.comap_rel, MulAction.orbitRel_apply, MulAction.mem_orbit_iff,
      Subtype.ext_iff, conjAct_smul_relationSet_coe]

/-- `relationModuliHomeomorphOrbitQuotient` sends `relationModuliMk x` to `Quotient.mk _ x`. -/
@[simp]
theorem relationModuliHomeomorphOrbitQuotient_mk {r : ℕ} {ζ : ℂ} {g : ℕ}
    (x : relationSet r ζ g) :
    relationModuliHomeomorphOrbitQuotient r ζ g (relationModuliMk x) = Quotient.mk _ x :=
  (rfl)

/-- The quotient projection `relationModuliMk` is an open quotient map, since `ConjAct (SU(r))`
acts by homeomorphisms on `relationSet r ζ g`. -/
theorem isOpenQuotientMap_relationModuliMk (r : ℕ) (ζ : ℂ) (g : ℕ) :
    IsOpenQuotientMap (@relationModuliMk r ζ g) := by
  have hcomp : (relationModuliHomeomorphOrbitQuotient r ζ g).symm ∘
      (Quotient.mk _ : relationSet r ζ g →
        MulAction.orbitRel.Quotient (ConjAct (Matrix.specialUnitaryGroup (Fin r) ℂ))
          (relationSet r ζ g)) = @relationModuliMk r ζ g :=
    funext fun x => (relationModuliHomeomorphOrbitQuotient r ζ g).symm_apply_apply
      (relationModuliMk x)
  rw [← hcomp]
  exact (relationModuliHomeomorphOrbitQuotient r ζ g).symm.isOpenQuotientMap.comp
    MulAction.isOpenQuotientMap_quotientMk

/-! ### Compactness and Hausdorffness -/

/-- Continuity of the ordered commutator-product map from `Fin g → SU(r) × SU(r)` into
`Matrix (Fin r) (Fin r) ℂ`. -/
private theorem continuous_commutatorProd (r g : ℕ) :
    Continuous (fun x : Fin g →
        Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ =>
      ((List.ofFn fun j => ⁅(x j).1, (x j).2⁆).prod : Matrix (Fin r) (Fin r) ℂ)) := by
  refine continuous_subtype_val.comp ?_
  induction g with
  | zero =>
    simpa only [List.ofFn_zero, List.prod_nil] using continuous_const
  | succ g ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    have hhead : Continuous (fun x : Fin (g + 1) →
          Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ =>
        ⁅(x 0).1, (x 0).2⁆) := by
      simp only [commutatorElement_def]
      fun_prop
    have htail : Continuous (fun x : Fin (g + 1) →
          Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ =>
        (List.ofFn fun j : Fin g => ⁅(x j.succ).1, (x j.succ).2⁆).prod) :=
      ih.comp (continuous_pi fun j => continuous_apply j.succ)
    exact hhead.mul htail

/-- `relationSet r ζ g` is a closed subset of `Fin g → SU(r) × SU(r)`. -/
theorem isClosed_relationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    IsClosed (relationSet r ζ g) :=
  isClosed_singleton.preimage (continuous_commutatorProd r g)

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

/-- `relationModuli r ζ g` is Hausdorff: `relationModuliMk` is an open quotient map and the orbit
relation is the image of the compact space `SU(r) × relationSet r ζ g`, hence closed. -/
instance instT2SpaceRelationModuli (r : ℕ) (ζ : ℂ) (g : ℕ) :
    T2Space (relationModuli r ζ g) := by
  rw [t2Space_iff_of_isOpenQuotientMap (isOpenQuotientMap_relationModuliMk r ζ g)]
  let S := relationSet r ζ g
  let Φ : Matrix.specialUnitaryGroup (Fin r) ℂ × S → S × S :=
    fun p => (ConjAct.toConjAct p.1 • p.2, p.2)
  have hcont : Continuous Φ := by
    refine Continuous.prodMk (Continuous.subtype_mk (continuous_pi fun j => ?_) _) continuous_snd
    have hj : Continuous fun p : Matrix.specialUnitaryGroup (Fin r) ℂ × S => p.2.1 j :=
      (continuous_apply j).comp (continuous_subtype_val.comp continuous_snd)
    exact Continuous.prodMk
      ((continuous_fst.mul (continuous_fst.comp hj)).mul continuous_fst.inv)
      ((continuous_fst.mul (continuous_snd.comp hj)).mul continuous_fst.inv)
  have hrange : {q : S × S | relationModuliMk q.1 = relationModuliMk q.2} = Set.range Φ := by
    ext ⟨a, b⟩
    simp only [Set.mem_ofPred_eq, relationModuliMk_eq_iff, Set.mem_range, Prod.ext_iff, Φ]
    refine ⟨fun ⟨u, hu⟩ => ⟨(u, b), Subtype.ext hu, rfl⟩,
      fun ⟨⟨u, b'⟩, ha, hb⟩ => ?_⟩
    subst hb
    exact ⟨u, congrArg Subtype.val ha⟩
  rw [hrange]
  exact (isCompact_range hcont).isClosed

/-! ### Centrality of stabilizers and the free `PSU(r)` action -/

/-- Restricting the identity matrix to `{i : Fin r // p i}` yields the identity matrix. -/
private theorem submatrix_subtype_one {r : ℕ} (p : Fin r → Prop) :
    (1 : Matrix (Fin r) (Fin r) ℂ).submatrix (Subtype.val : {i : Fin r // p i} → Fin r)
      (Subtype.val : {i : Fin r // p i} → Fin r) = 1 :=
  submatrix_one _ Subtype.val_injective

/-- Restricting `ζ • 1` to `{i : Fin r // p i}` yields `ζ • 1`. -/
private theorem submatrix_subtype_smul_one {r : ℕ} (p : Fin r → Prop) (ζ : ℂ) :
    (ζ • (1 : Matrix (Fin r) (Fin r) ℂ)).submatrix (Subtype.val : {i : Fin r // p i} → Fin r)
      (Subtype.val : {i : Fin r // p i} → Fin r) = ζ • 1 :=
  congrArg (ζ • ·) (submatrix_subtype_one p)

/-- If a matrix `M` commutes with `diagonal d`, restricting to `{i // d i = c}` commutes with left
multiplication by `M` because all off-block entries of `M` vanish. -/
private theorem submatrix_mul_of_commute_diagonal {r : ℕ} {d : Fin r → ℂ} {c : ℂ}
    {M : Matrix (Fin r) (Fin r) ℂ} (hM : Commute (diagonal d) M)
    (N : Matrix (Fin r) (Fin r) ℂ) :
    (M * N).submatrix (Subtype.val : {i : Fin r // d i = c} → Fin r)
        (Subtype.val : {i : Fin r // d i = c} → Fin r) =
      M.submatrix (Subtype.val : {i : Fin r // d i = c} → Fin r)
          (Subtype.val : {i : Fin r // d i = c} → Fin r) *
        N.submatrix (Subtype.val : {i : Fin r // d i = c} → Fin r)
          (Subtype.val : {i : Fin r // d i = c} → Fin r) := by
  ext a b
  simp only [submatrix_apply, Matrix.mul_apply]
  rw [← Finset.sum_subtype (Finset.univ.filter fun k : Fin r => d k = c) (by simp)
    (fun k => M a.1 k * N k b.1)]
  symm
  refine Fintype.sum_subset fun k hk => ?_
  simp only [Finset.mem_univ, Finset.mem_filter, true_and]
  by_contra hne
  exact hk (by simp [apply_eq_zero_of_commute_diagonal hM (a.2.trans_ne (Ne.symm hne))])

/-- On any eigenspace `{i // d i = c}` of `diagonal d`, the block restriction of a commutator of
two special unitary matrices commuting with `diagonal d` has determinant `1`. -/
private theorem det_submatrix_commutator_eq_one {r : ℕ} {d : Fin r → ℂ} {c : ℂ}
    {A B : Matrix.specialUnitaryGroup (Fin r) ℂ}
    (hA : Commute (diagonal d) (A : Matrix (Fin r) (Fin r) ℂ))
    (hB : Commute (diagonal d) (B : Matrix (Fin r) (Fin r) ℂ)) :
    (((⁅A, B⁆ : Matrix.specialUnitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ).submatrix
      (Subtype.val : {i : Fin r // d i = c} → Fin r)
      (Subtype.val : {i : Fin r // d i = c} → Fin r)).det = 1 := by
  let sub : Matrix (Fin r) (Fin r) ℂ → Matrix {i : Fin r // d i = c} {i : Fin r // d i = c} ℂ :=
    fun M => M.submatrix Subtype.val Subtype.val
  have hinv_comm : ∀ {G : Matrix.specialUnitaryGroup (Fin r) ℂ},
      Commute (diagonal d) (G : Matrix (Fin r) (Fin r) ℂ) →
      Commute (diagonal d) ((G⁻¹ : Matrix.specialUnitaryGroup (Fin r) ℂ) :
        Matrix (Fin r) (Fin r) ℂ) ∧ (sub G).det * (sub (G⁻¹ : _)).det = 1 := by
    intro G hG
    have h1 : (G : Matrix (Fin r) (Fin r) ℂ) * (G⁻¹ : Matrix.specialUnitaryGroup (Fin r) ℂ) = 1 :=
      by rw [← Submonoid.coe_mul, mul_inv_cancel, OneMemClass.coe_one]
    have h2 : ((G⁻¹ : Matrix.specialUnitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * G = 1 :=
      by rw [← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one]
    have hGinv : Commute (diagonal d)
        ((G⁻¹ : Matrix.specialUnitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) := by
      calc diagonal d * (G⁻¹ : Matrix.specialUnitaryGroup (Fin r) ℂ)
          = (((G⁻¹ : Matrix.specialUnitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * G) *
              (diagonal d * (G⁻¹ : Matrix.specialUnitaryGroup (Fin r) ℂ)) := by
            rw [h2, Matrix.one_mul]
        _ = ((G⁻¹ : Matrix.specialUnitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *
              (G * diagonal d) * (G⁻¹ : Matrix.specialUnitaryGroup (Fin r) ℂ) := by
            simp only [Matrix.mul_assoc]
        _ = (G⁻¹ : Matrix.specialUnitaryGroup (Fin r) ℂ) * diagonal d := by
            rw [← hG.eq, Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_one]
    refine ⟨hGinv, ?_⟩
    rw [← det_mul, ← submatrix_mul_of_commute_diagonal hG, h1, submatrix_subtype_one, det_one]
  obtain ⟨hAinv, hAdet⟩ := hinv_comm hA
  obtain ⟨_, hBdet⟩ := hinv_comm hB
  rw [commutatorElement_def, Submonoid.coe_mul, Submonoid.coe_mul, Submonoid.coe_mul,
    Matrix.mul_assoc, Matrix.mul_assoc, submatrix_mul_of_commute_diagonal hA,
    submatrix_mul_of_commute_diagonal hB, submatrix_mul_of_commute_diagonal hAinv,
    det_mul, det_mul, det_mul]
  linear_combination (sub A).det * (sub (A⁻¹ : _)).det * hBdet + hAdet

/-- On `{i // d i = c}`, the block restriction of a list product of matrices commuting with
`diagonal d` whose block restrictions each have determinant `1` also has determinant `1`. -/
private theorem det_submatrix_list_prod_eq_one {r : ℕ} {d : Fin r → ℂ} {c : ℂ} :
    ∀ L : List (Matrix.specialUnitaryGroup (Fin r) ℂ),
      (∀ M ∈ L, Commute (diagonal d) (M : Matrix (Fin r) (Fin r) ℂ) ∧
        ((M : Matrix (Fin r) (Fin r) ℂ).submatrix
          (Subtype.val : {i : Fin r // d i = c} → Fin r)
          (Subtype.val : {i : Fin r // d i = c} → Fin r)).det = 1) →
      (((L.prod : Matrix.specialUnitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ).submatrix
        (Subtype.val : {i : Fin r // d i = c} → Fin r)
        (Subtype.val : {i : Fin r // d i = c} → Fin r)).det = 1
  | [], _ => by simp [submatrix_subtype_one]
  | M :: L, hL => by
    obtain ⟨hM_comm, hM_det⟩ := hL M List.mem_cons_self
    have ih := det_submatrix_list_prod_eq_one L fun N hN => hL N (List.mem_cons_of_mem M hN)
    rw [List.prod_cons, Submonoid.coe_mul, submatrix_mul_of_commute_diagonal hM_comm,
      det_mul, hM_det, ih, mul_one]

/-- If `ζ ^ card {i : Fin r // d i = d i₀} = 1` for a primitive `r`-th root of unity `ζ`, then `d`
is constant on `Fin r`. -/
private theorem eq_const_of_pow_card_subtype_eq_one {r : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ r)
    {d : Fin r → ℂ} (i₀ : Fin r)
    (hpow : ζ ^ Fintype.card {i : Fin r // d i = d i₀} = 1) :
    ∀ i : Fin r, d i = d i₀ := by
  let S := {i : Fin r // d i = d i₀}
  have hpos : 0 < Fintype.card S := Fintype.card_pos_iff.mpr ⟨⟨i₀, rfl⟩⟩
  have hle : Fintype.card S ≤ r := by
    simpa only [Fintype.card_fin] using Fintype.card_subtype_le (fun i : Fin r => d i = d i₀)
  have hcard : Fintype.card S = r :=
    le_antisymm hle (Nat.le_of_dvd hpos (hζ.dvd_of_pow_eq_one _ hpow))
  have huniv : Finset.univ.filter (fun i : Fin r => d i = d i₀) = Finset.univ :=
    Finset.eq_univ_of_card _ (by simpa [S, Fintype.card_subtype] using hcard)
  intro i
  have hi : i ∈ Finset.univ.filter (fun k : Fin r => d k = d i₀) :=
    huniv.symm ▸ Finset.mem_univ i
  simpa using hi

/-- **Centrality of stabilizers on `relationSet`.** When `ζ` is a primitive `r`-th root of unity,
every `u ∈ SU(r)` commuting with all entries of a solution `x ∈ relationSet r ζ g` lies in the
center of `SU(r)`. No positivity assumption on `r` or `g` is needed: for `r = 0`, `SU(0)` is
trivial, while for `g = 0` and `r ≥ 2`, `relationSet r ζ 0` is empty. -/
theorem relationSet_stabilizer_central {r : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ r) {g : ℕ}
    {x : Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ}
    (hx : x ∈ relationSet r ζ g) {u : Matrix.specialUnitaryGroup (Fin r) ℂ}
    (hu : ∀ j, Commute u (x j).1 ∧ Commute u (x j).2) :
    u ∈ Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact Subsingleton.elim u 1 ▸ Subgroup.one_mem _
  obtain ⟨w, z, hw⟩ := Matrix.specialUnitaryGroup.exists_conj_eq_diagonal u
  let u' : Matrix.specialUnitaryGroup (Fin r) ℂ := w * u * w⁻¹
  let x' := ConjAct.toConjAct w • x
  let d : Fin r → ℂ := fun i => (z i : ℂ)
  have hcomm_d : ∀ {y : Matrix.specialUnitaryGroup (Fin r) ℂ}, Commute u y →
      Commute (diagonal d) ((w * y * w⁻¹ : Matrix.specialUnitaryGroup (Fin r) ℂ) :
        Matrix (Fin r) (Fin r) ℂ) := by
    intro y hy
    have hc : Commute u' (w * y * w⁻¹) := hy.map (MulAut.conj w).toMonoidHom
    dsimp only [Commute, SemiconjBy]
    rw [← hw, ← Submonoid.coe_mul, ← Submonoid.coe_mul]
    exact congrArg Subtype.val hc.eq
  let i₀ : Fin r := ⟨0, hr⟩
  have hdet1 : ((((List.ofFn fun j => ⁅(x' j).1, (x' j).2⁆).prod :
        Matrix.specialUnitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ).submatrix
      (Subtype.val : {i : Fin r // d i = d i₀} → Fin r)
      (Subtype.val : {i : Fin r // d i = d i₀} → Fin r)).det = 1 := by
    refine det_submatrix_list_prod_eq_one _ fun M hM => ?_
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hM
    have hc : Commute u ⁅(x j).1, (x j).2⁆ := by
      rw [commutatorElement_def]
      exact (((hu j).1.mul_right (hu j).2).mul_right (hu j).1.inv_right).mul_right
        (hu j).2.inv_right
    have hcj : (w * ⁅(x j).1, (x j).2⁆ * w⁻¹ : Matrix.specialUnitaryGroup (Fin r) ℂ) =
        ⁅(x' j).1, (x' j).2⁆ := map_commutatorElement (MulAut.conj w).toMonoidHom _ _
    exact ⟨hcj ▸ hcomm_d hc, det_submatrix_commutator_eq_one (hcomm_d (hu j).1) (hcomm_d (hu j).2)⟩
  have hx' : x' ∈ relationSet r ζ g := conjAct_smul_mem_relationSet (ConjAct.toConjAct w) hx
  rw [mem_relationSet_iff.mp hx', submatrix_subtype_smul_one, det_smul, det_one,
    mul_one] at hdet1
  have hu'_center : u' ∈ Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) :=
    Matrix.specialUnitaryGroup.mem_center_of_coe_eq_scalar
      (by rw [hw, scalar_apply]; exact congrArg diagonal (funext
        (eq_const_of_pow_card_subtype_eq_one hζ i₀ hdet1)))
  have hu_eq : u = w⁻¹ * u' * w := by simp [u', mul_assoc]
  rw [hu_eq, Subgroup.mem_center_iff.mp hu'_center w⁻¹, inv_mul_cancel_right]
  exact hu'_center

/-- Central elements of `SU(r)` act trivially under simultaneous conjugation. -/
theorem conjAct_toConjAct_smul_eq_self_of_mem_center {r g : ℕ}
    {u : Matrix.specialUnitaryGroup (Fin r) ℂ}
    (hu : u ∈ Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ))
    (x : Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ) :
    ConjAct.toConjAct u • x = x := by
  funext j
  exact Prod.ext
    (by simp only [Pi.smul_apply, Prod.smul_fst, ConjAct.smul_def, ConjAct.ofConjAct_toConjAct]
        rw [← Subgroup.mem_center_iff.mp hu (x j).1, mul_inv_cancel_right])
    (by simp only [Pi.smul_apply, Prod.smul_snd, ConjAct.smul_def, ConjAct.ofConjAct_toConjAct]
        rw [← Subgroup.mem_center_iff.mp hu (x j).2, mul_inv_cancel_right])

/-- **Exact conjugation stabilizers on `relationSet`.** When `IsPrimitiveRoot ζ r`, an element of
`SU(r)` fixes `x ∈ relationSet r ζ g` under simultaneous conjugation if and only if it lies in the
center of `SU(r)`. -/
theorem conjAct_toConjAct_smul_eq_self_iff_mem_center {r : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ r) {g : ℕ}
    {x : Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ}
    (hx : x ∈ relationSet r ζ g) (u : Matrix.specialUnitaryGroup (Fin r) ℂ) :
    ConjAct.toConjAct u • x = x ↔
      u ∈ Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) := by
  refine ⟨fun h => relationSet_stabilizer_central hζ hx fun j => ?_,
    fun hu => conjAct_toConjAct_smul_eq_self_of_mem_center hu x⟩
  have hj1 := congrArg Prod.fst (congrFun h j)
  have hj2 := congrArg Prod.snd (congrFun h j)
  simp only [Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, ConjAct.smul_def,
    ConjAct.ofConjAct_toConjAct, mul_inv_eq_iff_eq_mul] at hj1 hj2
  exact ⟨hj1, hj2⟩

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
      exact conjAct_toConjAct_smul_eq_self_of_mem_center hu x.1

/-- A coset `QuotientGroup.mk u` in `SU(r) ⧸ center(SU(r))` acts on `relationSet r ζ g` by
simultaneous conjugation by `u`. -/
@[simp]
theorem quotientCenter_mk_smul_coe {r : ℕ} {ζ : ℂ} {g : ℕ}
    (u : Matrix.specialUnitaryGroup (Fin r) ℂ) (x : relationSet r ζ g) :
    (((QuotientGroup.mk u : Matrix.specialUnitaryGroup (Fin r) ℂ ⧸
        Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ)) • x : relationSet r ζ g) :
      Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ) =
      ConjAct.toConjAct u • x.1 :=
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
    have hfix : ConjAct.toConjAct (u₁⁻¹ * u₂) • x.1 = x.1 := by
      rw [map_mul, mul_smul, map_inv, inv_smul_eq_iff]
      simpa only [quotientCenter_mk_smul_coe] using (congrArg Subtype.val h).symm
    exact (conjAct_toConjAct_smul_eq_self_iff_mem_center hζ x.2 (u₁⁻¹ * u₂)).mp hfix

/-- Homeomorphism identifying `relationModuli r ζ g` with the orbit quotient of the effective
`SU(r) ⧸ Subgroup.center (SU(r))` action on `relationSet r ζ g`. -/
noncomputable def relationModuliHomeomorphQuotientCenter (r : ℕ) (ζ : ℂ) (g : ℕ) :
    relationModuli r ζ g ≃ₜ
      MulAction.orbitRel.Quotient
        (Matrix.specialUnitaryGroup (Fin r) ℂ ⧸
          Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ))
        (relationSet r ζ g) :=
  Homeomorph.Quotient.congrRight fun x y => by
    rw [Setoid.comap_rel]
    simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff,
      QuotientGroup.mk_surjective.exists, Subtype.ext_iff, quotientCenter_mk_smul_coe]
    exact ConjAct.toConjAct.toEquiv.exists_congr_left

/-! ### Sphere emptiness, low rank, and central holonomy twists -/

/-- On the sphere (`g = 0`), `relationSet r ζ 0` is empty whenever `1 ≤ r` and `ζ ≠ 1`. -/
theorem isEmpty_relationSet_zero {r : ℕ} (hr : 1 ≤ r) {ζ : ℂ} (hζ : ζ ≠ 1) :
    IsEmpty (relationSet r ζ 0) :=
  ⟨fun ⟨_, hx⟩ => hζ <| by
    have h := congr_fun₂ (mem_relationSet_zero_iff.mp hx) ⟨0, hr⟩ ⟨0, hr⟩
    simpa using h.symm⟩

/-- On the sphere (`g = 0`), `relationModuli r ζ 0` is empty whenever `1 ≤ r` and `ζ ≠ 1`. -/
theorem isEmpty_relationModuli_zero {r : ℕ} (hr : 1 ≤ r) {ζ : ℂ} (hζ : ζ ≠ 1) :
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
  have hsubSU : Subsingleton (Matrix.specialUnitaryGroup (Fin r) ℂ) := by
    refine ⟨fun A B => Subtype.ext ?_⟩
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hr with rfl | rfl
    · exact Subsingleton.elim _ _
    · have hA := (mem_specialUnitaryGroup_iff.mp A.2).2
      have hB := (mem_specialUnitaryGroup_iff.mp B.2).2
      rw [det_fin_one] at hA hB
      ext i j
      rw [Fin.eq_zero i, Fin.eq_zero j, hA, hB]
  have : Subsingleton (relationSet r ζ g) :=
    ⟨fun _ _ => Subtype.ext (funext fun _ => Prod.ext (hsubSU.elim _ _) (hsubSU.elim _ _))⟩
  infer_instance

/-- At `ζ = 1`, the trivial tuple `(1, 1, …, 1, 1)` lies in `relationSet r 1 g` for all `r` and
`g`. -/
instance instNonemptyRelationSetUntwisted (r g : ℕ) :
    Nonempty (relationSet r 1 g) :=
  ⟨⟨fun _ => (1, 1), by simp [mem_relationSet_iff, List.ofFn_const]⟩⟩

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
  rw [mem_relationSet_iff] at hx ⊢
  have hcomm_eq : ∀ j : Fin g,
      ⁅((ε j).1 : Matrix.specialUnitaryGroup (Fin r) ℂ) * (x j).1,
        ((ε j).2 : Matrix.specialUnitaryGroup (Fin r) ℂ) * (x j).2⁆ =
      ⁅(x j).1, (x j).2⁆ := fun j => by
    let c₁ : Matrix.specialUnitaryGroup (Fin r) ℂ := (ε j).1
    let c₂ : Matrix.specialUnitaryGroup (Fin r) ℂ := (ε j).2
    have hc₂ := Subgroup.mem_center_iff.mp (ε j).2.2
    have hc₁_inv := Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ (ε j).1.2)
    have hcomm1 : (x j).1 * (x j).2 * (x j).1⁻¹ * c₁⁻¹ =
        c₁⁻¹ * ((x j).1 * (x j).2 * (x j).1⁻¹) :=
      hc₁_inv ((x j).1 * (x j).2 * (x j).1⁻¹)
    rw [commutatorElement_def, commutatorElement_def, _root_.mul_inv_rev, _root_.mul_inv_rev]
    calc c₁ * (x j).1 * (c₂ * (x j).2) * ((x j).1⁻¹ * c₁⁻¹) * ((x j).2⁻¹ * c₂⁻¹)
        = c₂ * (c₁ * ((x j).1 * (x j).2 * (x j).1⁻¹ * c₁⁻¹)) * (x j).2⁻¹ * c₂⁻¹ := by
          simp only [← mul_assoc]
          rw [hc₂ (c₁ * (x j).1), ← mul_assoc]
      _ = c₂ * ((x j).1 * (x j).2 * (x j).1⁻¹) * (x j).2⁻¹ * c₂⁻¹ := by
          rw [hcomm1, ← mul_assoc c₁, mul_inv_cancel, one_mul]
      _ = (x j).1 * (x j).2 * (x j).1⁻¹ * (x j).2⁻¹ := by
          rw [mul_assoc c₂, ← hc₂ ((x j).1 * (x j).2 * (x j).1⁻¹ * (x j).2⁻¹),
            mul_assoc, mul_inv_cancel, mul_one]
  simpa only [hcomm_eq] using hx

/-- Scalar multiplication of central holonomy twists `Fin g → center(SU(r)) × center(SU(r))` on
`relationSet r ζ g` by entrywise multiplication. -/
noncomputable instance instSMulCenterTwistRelationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    SMul (Fin g → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
      Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ)) (relationSet r ζ g) where
  smul ε x := ⟨fun j => (((ε j).1 : Matrix.specialUnitaryGroup (Fin r) ℂ) * (x.1 j).1,
      ((ε j).2 : Matrix.specialUnitaryGroup (Fin r) ℂ) * (x.1 j).2),
    centerTwist_mem_relationSet ε x.2⟩

/-- Coercing a central twist `ε • x` from `relationSet r ζ g` multiplies each pair `(A_j, B_j)`
entrywise by `((ε j).1, (ε j).2)`. -/
@[simp]
theorem centerTwist_smul_relationSet_coe {r : ℕ} {ζ : ℂ} {g : ℕ}
    (ε : Fin g → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
      Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ)) (x : relationSet r ζ g) :
    ((ε • x : relationSet r ζ g) :
      Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ) =
      fun j => (((ε j).1 : Matrix.specialUnitaryGroup (Fin r) ℂ) * (x.1 j).1,
        ((ε j).2 : Matrix.specialUnitaryGroup (Fin r) ℂ) * (x.1 j).2) :=
  (rfl)

/-- The group `Fin g → center(SU(r)) × center(SU(r))` of central holonomy twists acts on
`relationSet r ζ g` by entrywise multiplication. -/
noncomputable instance instMulActionCenterTwistRelationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    MulAction (Fin g → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
      Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ)) (relationSet r ζ g) where
  one_smul x := Subtype.ext <| by simp [centerTwist_smul_relationSet_coe]
  mul_smul ε₁ ε₂ x := Subtype.ext <| by simp [centerTwist_smul_relationSet_coe, mul_assoc]

/-- The central holonomy twist action on `relationSet r ζ g` is jointly continuous. -/
instance instContinuousSMulCenterTwistRelationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    ContinuousSMul (Fin g → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
      Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ)) (relationSet r ζ g) where
  continuous_smul := continuous_induced_rng.2 <| by
    simp only [Function.comp_def, centerTwist_smul_relationSet_coe]
    refine continuous_pi fun j => Continuous.prodMk ?_ ?_
    · exact ((continuous_subtype_val.comp (continuous_fst.comp ((continuous_apply j).comp
        continuous_fst))).mul (continuous_fst.comp ((continuous_apply j).comp
        (continuous_subtype_val.comp continuous_snd))))
    · exact ((continuous_subtype_val.comp (continuous_snd.comp ((continuous_apply j).comp
        continuous_fst))).mul (continuous_snd.comp ((continuous_apply j).comp
        (continuous_subtype_val.comp continuous_snd))))

/-- Entrywise central twisting commutes with simultaneous `SU(r)`-conjugation, so it descends to a
group action on `relationModuli r ζ g`. -/
noncomputable instance instMulActionCenterTwistRelationModuli (r : ℕ) (ζ : ℂ) (g : ℕ) :
    MulAction (Fin g → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
      Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ)) (relationModuli r ζ g) where
  smul ε := Quotient.map' (ε • ·) fun x y ⟨u, hu⟩ => ⟨u, by
    let v := ConjAct.ofConjAct u
    funext j
    apply Prod.ext
    · have hj : v * (y.1 j).1 * v⁻¹ = (x.1 j).1 := congrArg Prod.fst (congrFun hu j)
      simp only [centerTwist_smul_relationSet_coe, Pi.smul_apply, Prod.smul_fst, ConjAct.smul_def]
      calc v * ((ε j).1.1 * (y.1 j).1) * v⁻¹
          = ((ε j).1.1 * v) * (y.1 j).1 * v⁻¹ := by
            rw [← mul_assoc v, (Subgroup.mem_center_iff.mp (ε j).1.2 v).symm]
        _ = (ε j).1.1 * (v * (y.1 j).1 * v⁻¹) := by simp only [mul_assoc]
        _ = (ε j).1.1 * (x.1 j).1 := by rw [hj]
    · have hj : v * (y.1 j).2 * v⁻¹ = (x.1 j).2 := congrArg Prod.snd (congrFun hu j)
      simp only [centerTwist_smul_relationSet_coe, Pi.smul_apply, Prod.smul_snd, ConjAct.smul_def]
      calc v * ((ε j).2.1 * (y.1 j).2) * v⁻¹
          = ((ε j).2.1 * v) * (y.1 j).2 * v⁻¹ := by
            rw [← mul_assoc v, (Subgroup.mem_center_iff.mp (ε j).2.2 v).symm]
        _ = (ε j).2.1 * (v * (y.1 j).2 * v⁻¹) := by simp only [mul_assoc]
        _ = (ε j).2.1 * (x.1 j).2 := by rw [hj]⟩
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
    exact (continuous_relationModuliMk r ζ g).comp continuous_smul

end TauCeti.SpecialUnitary
