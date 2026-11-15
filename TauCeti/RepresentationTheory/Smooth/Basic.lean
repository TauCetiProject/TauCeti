/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Stabilizer
public import TauCeti.RepresentationTheory.Intertwining
public import TauCeti.RepresentationTheory.Pi
public import TauCeti.RepresentationTheory.Subrepresentation
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.Compact
import TauCeti.GroupTheory.QuotientGroup.Basic

/-!
# Smooth representations and smooth vectors

Let `G` be a group carrying a topology and `ρ : Representation A G V` a representation of `G` on an
`A`-module `V`, with no topology on `V`. The representation `ρ` is *smooth*
(`Representation.IsSmooth ρ`) when every vector `v : V` has open stabilizer
`ρ.stabilizer v = {g : G | ρ g v = v}` in `G`.

When multiplication in `G` is separately continuous (in particular, in any topological group), a
subgroup containing an open subgroup is open and conjugation by any element of `G` is a
homeomorphism. Consequently:

* `ρ` is smooth if and only if every vector is fixed by some open subgroup
  (`Representation.isSmooth_iff_exists_openSubgroup`);
* the vectors with open stabilizer form a subrepresentation `ρ.smoothVectors : Subrepresentation ρ`
  whose restricted representation is smooth (`Representation.smoothVectors_eq_top_iff`,
  `Subrepresentation.instIsSmoothToRepresentation`);
* `ρ.smoothVectors` is the largest smooth subrepresentation of `ρ`
  (`Representation.le_smoothVectors_iff`) and is functorial in intertwining maps
  (`Representation.IntertwiningMap.restrictSmoothVectors`);
* smoothness is preserved by subrepresentations, quotients, finite products, arbitrary direct sums,
  and restriction along continuous group homomorphisms, and holds for permutation representations
  `Representation.ofMulAction A G (G ⧸ U.toSubgroup)` attached to open subgroups `U`.

When `G` is weakly locally compact and zero-dimensional — in particular, for any locally profinite
group (Hausdorff, locally compact, and totally disconnected) — van Dantzig's theorem refines open
stabilizers to compact open subgroups: a vector is smooth if and only if it lies in the
`U`-invariants `invariants (ρ.comp U.toSubgroup.subtype)` for some compact open subgroup `U`, so
`ρ.smoothVectors` is the directed union (and submodule supremum) of `V^U` over compact open
subgroups `U`, and `ρ` is smooth if and only if these invariants exhaust `V`
(`Representation.mem_smoothVectors_iff_exists_isCompact_openSubgroup`,
`Representation.smoothVectors_toSubmodule_eq_iSup_invariants_isCompact`,
`Representation.isSmooth_iff_iSup_invariants_isCompact_eq_top`).

For the left regular representation `Representation.leftRegular A G` on `A[G]`, every nonzero
vector has finite stabilizer (`Representation.finite_stabilizer_leftRegular_of_ne_zero`). In a
non-discrete `T₁` group with separately continuous multiplication, no open subgroup is finite, so
`(leftRegular A G).smoothVectors = ⊥` (`Representation.smoothVectors_leftRegular_eq_bot`) and the
left regular representation over a nontrivial coefficient ring is smooth if and only if `G` is
discrete (`Representation.isSmooth_leftRegular_iff_discreteTopology`).

## Main definitions

* `Representation.IsSmooth`: typeclass asserting that every vector of `ρ` has open stabilizer.
* `Representation.IsSmooth.openStabilizer`: the stabilizer of `v` bundled as an `OpenSubgroup G`.
* `Representation.smoothVectors`: the subrepresentation `V^∞` of vectors with open stabilizer.
* `Representation.IntertwiningMap.restrictSmoothVectors`: action of an intertwining map on smooth
  vectors.
* `Representation.IntertwiningMap.liftSmoothVectorsEquiv`: universal property identifying
  intertwining maps from a smooth representation into `ρ'` with those into `ρ'.smoothVectors`.

## Main results

* `Representation.isSmooth_iff_exists_openSubgroup`,
  `Representation.isSmooth_iff_exists_isCompact_openSubgroup`,
  `Representation.isSmooth_iff_iSup_invariants_isCompact_eq_top`: characterizations of smoothness
  by open subgroups and, in the locally profinite case, compact open subgroup invariants.
* `Representation.mem_smoothVectors`, `Representation.smoothVectors_eq_top_iff`,
  `Representation.le_smoothVectors_iff`,
  `Representation.smoothVectors_toSubmodule_eq_iSup_invariants_isCompact`: characterizations and
  maximality of `ρ.smoothVectors`.
* `Subrepresentation.instIsSmoothToRepresentation`, `Subrepresentation.instIsSmoothQuotient`,
  `Representation.IsSmooth.prod`, `Representation.IsSmooth.pi_of_finite`,
  `Representation.IsSmooth.directSum`, `Representation.IsSmooth.comp`,
  `Representation.IsSmooth.ofMulAction_quotient`: permanence properties and standard smooth
  representations.
* `Representation.smoothVectors_leftRegular_eq_bot`,
  `Representation.isSmooth_leftRegular_iff_discreteTopology`: smooth vectors of the left regular
  representation.

## References

* J. N. Bernstein, *Representations of `p`-adic Groups*, Harvard University lecture notes written
  by K. E. Rumelhart (1992), Ch. I §1.1, Definition 2 and Proposition 1, p. 7.
-/

public section

open Filter Set Topology
open scoped MonoidAlgebra Pointwise

namespace Subrepresentation

variable {A G V : Type*} [Semiring A] [Group G] [AddCommMonoid V] [Module A V]
  {ρ : Representation A G V}

/-- Restricting a representation to a subrepresentation preserves the stabilizer of each vector. -/
@[simp]
theorem stabilizer_toRepresentation_eq (σ : Subrepresentation ρ) (v : σ.toSubmodule) :
    σ.toRepresentation.stabilizer v = ρ.stabilizer v.1 := by
  ext g
  simp [toRepresentation_apply_coe]

end Subrepresentation

namespace Representation

section StabilizerLemmas

variable {A G H V V' : Type*} [Semiring A] [Group G] [Group H]
  [AddCommMonoid V] [Module A V] [AddCommMonoid V'] [Module A V']

/-- Pulling a representation back along a group homomorphism pulls vector stabilizers back by
`Subgroup.comap`. -/
@[simp]
theorem stabilizer_comp (ρ : Representation A G V) (f : H →* G) (v : V) :
    stabilizer (ρ.comp f) v = (ρ.stabilizer v).comap f := by
  ext h
  simp

/-- The stabilizer of a pair in a binary product representation is the intersection of the
component stabilizers. -/
@[simp]
theorem stabilizer_prod (ρ : Representation A G V) (ρ' : Representation A G V') (x : V × V') :
    (ρ.prod ρ').stabilizer x = ρ.stabilizer x.1 ⊓ ρ'.stabilizer x.2 := by
  ext g
  simp [Prod.ext_iff]

/-- The stabilizer of a tuple in a product representation is the infimum of the coordinate
stabilizers. -/
@[simp]
theorem stabilizer_pi {ι : Type*} {W : ι → Type*} [∀ i, AddCommMonoid (W i)] [∀ i, Module A (W i)]
    (ρ : ∀ i, Representation A G (W i)) (x : ∀ i, W i) :
    (pi ρ).stabilizer x = ⨅ i, (ρ i).stabilizer (x i) := by
  ext g
  simp [funext_iff, Subgroup.mem_iInf]

/-- An injective intertwining map preserves vector stabilizers exactly. -/
theorem IntertwiningMap.stabilizer_eq_of_injective {ρ : Representation A G V}
    {ρ' : Representation A G V'} (f : ρ.IntertwiningMap ρ') (hf : Function.Injective f) (v : V) :
    ρ.stabilizer v = ρ'.stabilizer (f v) := by
  refine le_antisymm (f.stabilizer_le v) fun g hg ↦ ?_
  rw [mem_stabilizer] at hg ⊢
  exact hf (by simpa [← f.isIntertwining] using hg)

/-- In a quotient representation, the stabilizer of the image of `w` contains the stabilizer of
`w`. -/
theorem le_stabilizer_quotient_mk {R W : Type*} [Ring R] [AddCommGroup W] [Module R W]
    (ρ : Representation R G W) (N : Submodule R W) (hN : ∀ g : G, ∀ w ∈ N, ρ g w ∈ N) (w : W) :
    ρ.stabilizer w ≤ (ρ.quotient N hN).stabilizer (Submodule.Quotient.mk w) := by
  intro g hg
  rw [mem_stabilizer] at hg ⊢
  simp [hg]

/-- In a permutation representation `ofMulAction A G X`, the stabilizer of any monomial
`single x r` contains the action stabilizer of `x`. -/
theorem le_stabilizer_ofMulAction_single {X : Type*} [MulAction G X] (x : X) (r : A) :
    MulAction.stabilizer G x ≤ (ofMulAction A G X).stabilizer (MonoidAlgebra.single x r) := by
  intro g hg
  simp [MulAction.mem_stabilizer_iff.mp hg]

/-- In a permutation representation `ofMulAction A G X`, the stabilizer of a nonzero monomial
`single x r` (`r ≠ 0`) equals the action stabilizer of `x`. -/
@[simp]
theorem stabilizer_ofMulAction_single {X : Type*} [MulAction G X] (x : X) {r : A} (hr : r ≠ 0) :
    (ofMulAction A G X).stabilizer (MonoidAlgebra.single x r) = MulAction.stabilizer G x := by
  refine le_antisymm (fun g hg ↦ ?_) (le_stabilizer_ofMulAction_single x r)
  rw [mem_stabilizer, ofMulAction_single] at hg
  rw [MulAction.mem_stabilizer_iff]
  by_contra hne
  have hcoeff := congrArg (fun f : A[X] ↦ f.coeff x) hg
  rw [MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_single, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne' hne] at hcoeff
  exact hr hcoeff.symm

/-- If `N` is a normal subgroup of `G`, every element of `N` fixes every vector of the permutation
representation `A[G ⧸ N]`. -/
theorem ofMulAction_quotient_apply_of_mem {N : Subgroup G} [N.Normal] {g : G} (hg : g ∈ N)
    (f : A[G ⧸ N]) : ofMulAction A G (G ⧸ N) g f = f := by
  induction f using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single q r => simp [TauCeti.smul_quotient_eq_self_of_mem hg q]

/-- Every nonzero element of the left regular representation `A[G]` has finite stabilizer. -/
theorem finite_stabilizer_leftRegular_of_ne_zero {f : A[G]} (hf : f ≠ 0) :
    ((leftRegular A G).stabilizer f : Set G).Finite := by
  have hsupp : f.coeff.support.Nonempty := Finsupp.support_nonempty_iff.mpr fun h ↦
    hf ((MonoidAlgebra.coeffLinearEquiv A).injective (by simpa using h))
  obtain ⟨x₀, hx₀⟩ := hsupp
  have himg : (· * x₀) '' ((leftRegular A G).stabilizer f : Set G) ⊆ f.coeff.support := by
    rintro _ ⟨g, hg, rfl⟩
    have hginv : g⁻¹ ∈ (leftRegular A G).stabilizer f := inv_mem hg
    rw [mem_stabilizer] at hginv
    have hcoeff : f.coeff (g * x₀) = f.coeff x₀ := by
      have hc := congrArg (fun y : A[G] ↦ y.coeff x₀) hginv
      simpa [coeff_ofMulAction, inv_inv] using hc
    exact Finsupp.mem_support_iff.mpr (hcoeff ▸ Finsupp.mem_support_iff.mp hx₀)
  exact (f.coeff.support.finite_toSet.subset himg).of_finite_image (mul_left_injective x₀).injOn

end StabilizerLemmas

section IsSmooth

variable {A G V V' : Type*} [Semiring A] [Group G] [TopologicalSpace G]
  [AddCommMonoid V] [Module A V] [AddCommMonoid V'] [Module A V']

/-- A representation `ρ : Representation A G V` of a group `G` carrying a topology is *smooth* if
every vector `v : V` has open stabilizer in `G`. -/
class IsSmooth (ρ : Representation A G V) : Prop where
  /-- Every vector has open stabilizer in `G`. -/
  isOpen_stabilizer (v : V) : IsOpen (ρ.stabilizer v : Set G)

/-- Restatement of `Representation.IsSmooth` in terms of `Representation.stabilizer`. -/
theorem isSmooth_iff {ρ : Representation A G V} :
    ρ.IsSmooth ↔ ∀ v : V, IsOpen (ρ.stabilizer v : Set G) :=
  ⟨fun h ↦ h.isOpen_stabilizer, fun h ↦ ⟨h⟩⟩

/-- Restatement of `Representation.IsSmooth` directly as openness of `{g : G | ρ g v = v}`. -/
theorem isSmooth_iff_isOpen_setOf {ρ : Representation A G V} :
    ρ.IsSmooth ↔ ∀ v : V, IsOpen {g : G | ρ g v = v} :=
  isSmooth_iff

/-- In a smooth representation, the stabilizer of each vector bundled as an `OpenSubgroup G`. -/
def IsSmooth.openStabilizer (ρ : Representation A G V) [ρ.IsSmooth] (v : V) : OpenSubgroup G :=
  ⟨ρ.stabilizer v, IsSmooth.isOpen_stabilizer v⟩

@[simp]
theorem IsSmooth.mem_openStabilizer {ρ : Representation A G V} [ρ.IsSmooth] {v : V} {g : G} :
    g ∈ IsSmooth.openStabilizer ρ v ↔ ρ g v = v :=
  (Iff.rfl)

@[simp, norm_cast]
theorem IsSmooth.toSubgroup_openStabilizer (ρ : Representation A G V) [ρ.IsSmooth] (v : V) :
    (IsSmooth.openStabilizer ρ v : Subgroup G) = ρ.stabilizer v :=
  (rfl)

@[simp]
theorem IsSmooth.coe_openStabilizer (ρ : Representation A G V) [ρ.IsSmooth] (v : V) :
    (IsSmooth.openStabilizer ρ v : Set G) = (ρ.stabilizer v : Set G) :=
  (rfl)

/-- Every representation of a discrete group is smooth. -/
instance IsSmooth.of_discreteTopology [DiscreteTopology G] (ρ : Representation A G V) :
    ρ.IsSmooth where
  isOpen_stabilizer _ := isOpen_discrete _

/-- Every trivial representation is smooth. -/
instance IsSmooth.of_isTrivial (ρ : Representation A G V) [ρ.IsTrivial] : ρ.IsSmooth where
  isOpen_stabilizer v := by
    have htop : ρ.stabilizer v = ⊤ := by ext g; simp [ρ.isTrivial_apply]
    rw [htop]
    exact isOpen_univ

/-- Every representation on a subsingleton module is smooth. -/
instance IsSmooth.of_subsingleton [Subsingleton V] (ρ : Representation A G V) : ρ.IsSmooth where
  isOpen_stabilizer v := by
    have htop : ρ.stabilizer v = ⊤ := by ext g; simp [Subsingleton.elim (ρ g v) v]
    rw [htop]
    exact isOpen_univ

/-- Any subrepresentation of a smooth representation is smooth. -/
instance _root_.Subrepresentation.instIsSmoothToRepresentation {ρ : Representation A G V}
    (σ : Subrepresentation ρ) [ρ.IsSmooth] : σ.toRepresentation.IsSmooth where
  isOpen_stabilizer v := by
    rw [σ.stabilizer_toRepresentation_eq]
    exact IsSmooth.isOpen_stabilizer v.1

/-- Smoothness pulls back along an injective intertwining map. -/
theorem IsSmooth.of_injective {ρ : Representation A G V} {ρ' : Representation A G V'}
    (f : ρ.IntertwiningMap ρ') (hf : Function.Injective f) [ρ'.IsSmooth] : ρ.IsSmooth where
  isOpen_stabilizer v := by
    rw [f.stabilizer_eq_of_injective hf v]
    exact IsSmooth.isOpen_stabilizer (f v)

/-- Equivalent representations are simultaneously smooth. -/
theorem Equiv.isSmooth_iff {ρ : Representation A G V} {ρ' : Representation A G V'}
    (e : ρ.Equiv ρ') : ρ.IsSmooth ↔ ρ'.IsSmooth :=
  ⟨fun _ ↦ .of_injective e.symm.toIntertwiningMap e.symm.injective,
    fun _ ↦ .of_injective e.toIntertwiningMap e.injective⟩

/-- Restricting a smooth representation along a continuous homomorphism yields a smooth
representation. -/
theorem IsSmooth.comp {H : Type*} [Group H] [TopologicalSpace H] {ρ : Representation A G V}
    {f : H →* G} (hf : Continuous f) [ρ.IsSmooth] : IsSmooth (ρ.comp f) where
  isOpen_stabilizer v := by
    rw [stabilizer_comp]
    exact (IsSmooth.isOpen_stabilizer (ρ := ρ) v).preimage hf

/-- Restricting a smooth representation to any subgroup yields a smooth representation for the
subspace topology. -/
instance IsSmooth.comp_subtype (ρ : Representation A G V) [ρ.IsSmooth] (H : Subgroup G) :
    IsSmooth (ρ.comp H.subtype) :=
  IsSmooth.comp (f := H.subtype) continuous_subtype_val

/-- The binary product of two smooth representations is smooth. -/
instance IsSmooth.prod (ρ : Representation A G V) (ρ' : Representation A G V')
    [ρ.IsSmooth] [ρ'.IsSmooth] : (ρ.prod ρ').IsSmooth where
  isOpen_stabilizer x := by
    rw [stabilizer_prod]
    exact (IsSmooth.isOpen_stabilizer x.1).inter (IsSmooth.isOpen_stabilizer x.2)

/-- A finite product of smooth representations is smooth. -/
instance IsSmooth.pi_of_finite {ι : Type*} [Finite ι] {W : ι → Type*} [∀ i, AddCommMonoid (W i)]
    [∀ i, Module A (W i)] (ρ : ∀ i, Representation A G (W i)) [∀ i, (ρ i).IsSmooth] :
    (pi ρ).IsSmooth where
  isOpen_stabilizer x := by
    rw [stabilizer_pi, Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun i ↦ IsSmooth.isOpen_stabilizer (x i)

end IsSmooth

section SeparatelyContinuousMul

variable {A G V V' : Type*} [Semiring A] [Group G] [TopologicalSpace G]
  [SeparatelyContinuousMul G] [AddCommMonoid V] [Module A V] [AddCommMonoid V'] [Module A V']

/-- Conjugating an open subgroup by `g` preserves openness when multiplication is separately
continuous. -/
private theorem isOpen_map_conj {H : Subgroup G} (hH : IsOpen (H : Set G)) (g : G) :
    IsOpen ((H.map (MulAut.conj g) : Subgroup G) : Set G) := by
  have hpre : ((H.map (MulAut.conj g) : Subgroup G) : Set G) =
      (fun x ↦ g⁻¹ * x * g) ⁻¹' (H : Set G) := by
    ext x
    simp only [SetLike.mem_coe, Subgroup.mem_map, MonoidHom.coe_ofClass, MulAut.conj_apply,
      mem_preimage]
    exact ⟨by rintro ⟨y, hy, rfl⟩; simpa [mul_assoc] using hy,
      fun hx ↦ ⟨g⁻¹ * x * g, hx, by group⟩⟩
  rw [hpre]
  exact hH.preimage
    (((Homeomorph.mulRight g).continuous).comp (Homeomorph.mulLeft g⁻¹).continuous)

/-- Acting on a vector by `ρ g` preserves openness of its stabilizer. -/
theorem isOpen_stabilizer_apply (ρ : Representation A G V) {v : V}
    (hv : IsOpen (ρ.stabilizer v : Set G)) (g : G) :
    IsOpen (ρ.stabilizer (ρ g v) : Set G) := by
  rw [ρ.stabilizer_conj g v]
  exact isOpen_map_conj hv g

/-- The stabilizer of `ρ g v` is open if and only if the stabilizer of `v` is open. -/
@[simp]
theorem isOpen_stabilizer_apply_iff (ρ : Representation A G V) (g : G) (v : V) :
    IsOpen (ρ.stabilizer (ρ g v) : Set G) ↔ IsOpen (ρ.stabilizer v : Set G) :=
  ⟨fun h ↦ by simpa using ρ.isOpen_stabilizer_apply h g⁻¹, fun h ↦ ρ.isOpen_stabilizer_apply h g⟩

/-- In a group with separately continuous multiplication, a representation is smooth if and only if
every vector is fixed by some open subgroup. -/
theorem isSmooth_iff_exists_openSubgroup {ρ : Representation A G V} :
    ρ.IsSmooth ↔ ∀ v : V, ∃ U : OpenSubgroup G, ∀ g ∈ U, ρ g v = v :=
  ⟨fun h v ↦ ⟨⟨ρ.stabilizer v, h.isOpen_stabilizer v⟩, fun _ hg ↦ hg⟩,
    fun h ↦ ⟨fun v ↦ let ⟨_, hU⟩ := h v; (ρ.stabilizer v).isOpen_of_openSubgroup hU⟩⟩

/-- An intertwining map sends any vector with open stabilizer to a vector with open stabilizer. -/
theorem IntertwiningMap.isOpen_stabilizer_apply {ρ : Representation A G V}
    {ρ' : Representation A G V'} (f : ρ.IntertwiningMap ρ') {v : V}
    (hv : IsOpen (ρ.stabilizer v : Set G)) :
    IsOpen (ρ'.stabilizer (f v) : Set G) :=
  Subgroup.isOpen_mono (f.stabilizer_le v) hv

/-- Smoothness descends along a surjective intertwining map. -/
theorem IsSmooth.of_surjective {ρ : Representation A G V} {ρ' : Representation A G V'}
    (f : ρ.IntertwiningMap ρ') (hf : Function.Surjective f) [ρ.IsSmooth] : ρ'.IsSmooth where
  isOpen_stabilizer w := by
    obtain ⟨v, rfl⟩ := hf w
    exact f.isOpen_stabilizer_apply (IsSmooth.isOpen_stabilizer v)

/-- Any quotient representation of a smooth representation is smooth. -/
theorem IsSmooth.quotient {R W : Type*} [Ring R] [AddCommGroup W] [Module R W]
    (ρ : Representation R G W) [ρ.IsSmooth] (N : Submodule R W)
    (hN : ∀ g : G, ∀ w ∈ N, ρ g w ∈ N) : (ρ.quotient N hN).IsSmooth where
  isOpen_stabilizer q := by
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective N q
    exact Subgroup.isOpen_mono (ρ.le_stabilizer_quotient_mk N hN w) (IsSmooth.isOpen_stabilizer w)

/-- The quotient of a smooth representation by any subrepresentation is smooth. -/
instance _root_.Subrepresentation.instIsSmoothQuotient {R W : Type*} [Ring R] [AddCommGroup W]
    [Module R W] {ρ : Representation R G W} (σ : Subrepresentation ρ) [ρ.IsSmooth] :
    σ.quotient.IsSmooth :=
  IsSmooth.quotient ρ σ.toSubmodule (fun g _ hw ↦ σ.apply_mem_toSubmodule g hw)

/-- An arbitrary direct sum of smooth representations is smooth, since each element has finite
support. -/
instance IsSmooth.directSum {ι : Type*} {W : ι → Type*}
    [∀ i, AddCommMonoid (W i)] [∀ i, Module A (W i)]
    (ρ : ∀ i, Representation A G (W i)) [∀ i, (ρ i).IsSmooth] :
    (Representation.directSum ρ).IsSmooth where
  isOpen_stabilizer x := by
    classical
    have hle : (⨅ i ∈ x.support, (ρ i).stabilizer (x i)) ≤
        (Representation.directSum ρ).stabilizer x := by
      intro g hg
      rw [mem_stabilizer]
      ext i
      by_cases hi : i ∈ x.support
      · have hgi := Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hg i) hi
        simpa [DirectSum.lmap_apply] using mem_stabilizer.mp hgi
      · have hx0 : x i = 0 := DFinsupp.notMem_support_iff.mp hi
        simp [DirectSum.lmap_apply, hx0]
    refine Subgroup.isOpen_mono hle ?_
    simp only [Subgroup.coe_iInf]
    exact isOpen_biInter_finset fun i _ ↦ IsSmooth.isOpen_stabilizer (ρ := ρ i) (x i)

/-! ### The subrepresentation of smooth vectors -/

/-- The subrepresentation `V^∞` of *smooth vectors* of `ρ`: the vectors whose stabilizer in `G` is
open. Separate continuity of multiplication ensures closure under addition and `G`-translates. -/
def smoothVectors (ρ : Representation A G V) : Subrepresentation ρ where
  toSubmodule :=
    { carrier := {v : V | IsOpen (ρ.stabilizer v : Set G)}
      zero_mem' := by simp [stabilizer_zero]
      add_mem' {v₁ v₂} hv₁ hv₂ :=
        Subgroup.isOpen_mono (ρ.le_stabilizer_add v₁ v₂) (hv₁.inter hv₂)
      smul_mem' c {v} hv :=
        Subgroup.isOpen_mono (ρ.le_stabilizer_smul c v) hv }
  apply_mem_toSubmodule g {_} hv := ρ.isOpen_stabilizer_apply hv g

/-- A vector lies in `ρ.smoothVectors` if and only if its stabilizer in `G` is open. -/
@[simp]
theorem mem_smoothVectors {ρ : Representation A G V} {v : V} :
    v ∈ ρ.smoothVectors ↔ IsOpen (ρ.stabilizer v : Set G) :=
  (Iff.rfl)

/-- Restatement of membership in `ρ.smoothVectors` directly in terms of `{g : G | ρ g v = v}`. -/
theorem mem_smoothVectors_iff_isOpen_setOf {ρ : Representation A G V} {v : V} :
    v ∈ ρ.smoothVectors ↔ IsOpen {g : G | ρ g v = v} :=
  (Iff.rfl)

/-- A vector lies in `ρ.smoothVectors` if and only if it is fixed by some open subgroup of `G`. -/
theorem mem_smoothVectors_iff_exists_openSubgroup {ρ : Representation A G V} {v : V} :
    v ∈ ρ.smoothVectors ↔ ∃ U : OpenSubgroup G, ∀ g ∈ U, ρ g v = v :=
  ⟨fun hv ↦ ⟨⟨ρ.stabilizer v, hv⟩, fun _ hg ↦ hg⟩,
    fun ⟨_, hU⟩ ↦ (ρ.stabilizer v).isOpen_of_openSubgroup hU⟩

/-- Restricting `ρ` to its subrepresentation of smooth vectors yields a smooth representation. -/
instance instIsSmoothSmoothVectors (ρ : Representation A G V) :
    ρ.smoothVectors.toRepresentation.IsSmooth where
  isOpen_stabilizer v := by
    rw [ρ.smoothVectors.stabilizer_toRepresentation_eq]
    exact v.2

/-- The subrepresentation of smooth vectors equals `⊤` if and only if `ρ` is smooth. -/
theorem smoothVectors_eq_top_iff {ρ : Representation A G V} :
    ρ.smoothVectors = ⊤ ↔ ρ.IsSmooth := by
  rw [isSmooth_iff, ← Subrepresentation.toSubmodule_injective.eq_iff,
    Subrepresentation.toSubmodule_top, Submodule.eq_top_iff']
  rfl

/-- For a smooth representation, `ρ.smoothVectors = ⊤`. -/
@[simp]
theorem smoothVectors_eq_top (ρ : Representation A G V) [ρ.IsSmooth] :
    ρ.smoothVectors = ⊤ :=
  smoothVectors_eq_top_iff.mpr ‹_›

/-- Forming smooth vectors is idempotent: every vector of `ρ.smoothVectors.toRepresentation` is
already smooth. -/
theorem smoothVectors_toRepresentation (ρ : Representation A G V) :
    ρ.smoothVectors.toRepresentation.smoothVectors = ⊤ :=
  smoothVectors_eq_top _

/-- Maximality of `ρ.smoothVectors`: a subrepresentation `σ` is contained in `ρ.smoothVectors` if
and only if `σ.toRepresentation` is smooth. -/
theorem le_smoothVectors_iff {ρ : Representation A G V} {σ : Subrepresentation ρ} :
    σ ≤ ρ.smoothVectors ↔ σ.toRepresentation.IsSmooth := by
  rw [isSmooth_iff]
  refine ⟨fun h ⟨v, hv⟩ ↦ ?_, fun h v hv ↦ ?_⟩
  · rw [σ.stabilizer_toRepresentation_eq]
    exact mem_smoothVectors.mp (h hv)
  · have hopen := h ⟨v, hv⟩
    rwa [σ.stabilizer_toRepresentation_eq] at hopen

/-- Viewing `ρ.smoothVectors` as an `A[G]`-submodule recovers the `A[G]`-span of the vectors with
open stabilizer, since that subset is already an `A[G]`-submodule. -/
theorem asSubmodule_smoothVectors_eq_span {R W : Type*} [CommSemiring R] [AddCommMonoid W]
    [Module R W] (ρ : Representation R G W) :
    ρ.smoothVectors.asSubmodule =
      Submodule.span R[G] {w : ρ.asModule | IsOpen (ρ.stabilizer w : Set G)} :=
  (Submodule.span_eq ρ.smoothVectors.asSubmodule).symm

/-- Every intertwining map carries smooth vectors to smooth vectors. -/
theorem IntertwiningMap.apply_mem_smoothVectors {ρ : Representation A G V}
    {ρ' : Representation A G V'} (f : ρ.IntertwiningMap ρ') {v : V} (hv : v ∈ ρ.smoothVectors) :
    f v ∈ ρ'.smoothVectors :=
  f.isOpen_stabilizer_apply hv

/-- Every intertwining map out of a smooth representation lands in the smooth vectors of the
target. -/
theorem IntertwiningMap.apply_mem_smoothVectors_of_isSmooth {ρ : Representation A G V}
    {ρ' : Representation A G V'} [ρ.IsSmooth] (f : ρ.IntertwiningMap ρ') (v : V) :
    f v ∈ ρ'.smoothVectors :=
  f.apply_mem_smoothVectors <| by
    rw [smoothVectors_eq_top, ← Subrepresentation.mem_toSubmodule,
      Subrepresentation.toSubmodule_top]
    trivial

/-- Restriction of an intertwining map `f : ρ → ρ'` to the subrepresentations of smooth vectors. -/
def IntertwiningMap.restrictSmoothVectors {ρ : Representation A G V} {ρ' : Representation A G V'}
    (f : ρ.IntertwiningMap ρ') :
    ρ.smoothVectors.toRepresentation.IntertwiningMap ρ'.smoothVectors.toRepresentation :=
  (f.comp ρ.smoothVectors.subtype).codRestrict ρ'.smoothVectors fun v ↦ by
    simpa using f.apply_mem_smoothVectors v.2

@[simp]
theorem IntertwiningMap.coe_restrictSmoothVectors_apply {ρ : Representation A G V}
    {ρ' : Representation A G V'} (f : ρ.IntertwiningMap ρ')
    (v : ρ.smoothVectors.toSubmodule) :
    (f.restrictSmoothVectors v : V') = f v.1 := by
  simp [restrictSmoothVectors]

@[simp]
theorem IntertwiningMap.restrictSmoothVectors_id (ρ : Representation A G V) :
    (IntertwiningMap.id ρ).restrictSmoothVectors =
      IntertwiningMap.id ρ.smoothVectors.toRepresentation := by
  ext v
  simp [restrictSmoothVectors]

@[simp]
theorem IntertwiningMap.restrictSmoothVectors_comp {V'' : Type*} [AddCommMonoid V'']
    [Module A V''] {ρ : Representation A G V} {ρ' : Representation A G V'}
    {ρ'' : Representation A G V''} (g : ρ'.IntertwiningMap ρ'') (f : ρ.IntertwiningMap ρ') :
    (g.comp f).restrictSmoothVectors =
      g.restrictSmoothVectors.comp f.restrictSmoothVectors := by
  ext v
  simp [restrictSmoothVectors]

/-- Universal property of `smoothVectors` (coreflection at the representation level): when `ρ` is
smooth, composing with the inclusion `ρ'.smoothVectors.subtype` identifies intertwining maps
`ρ → ρ'.smoothVectors` bijectively with intertwining maps `ρ → ρ'`. -/
def IntertwiningMap.liftSmoothVectorsEquiv {ρ : Representation A G V} [ρ.IsSmooth]
    (ρ' : Representation A G V') :
    (ρ.IntertwiningMap ρ'.smoothVectors.toRepresentation) ≃ (ρ.IntertwiningMap ρ') where
  toFun g := ρ'.smoothVectors.subtype.comp g
  invFun f := f.codRestrict ρ'.smoothVectors fun v ↦
    Subrepresentation.mem_toSubmodule.mpr (f.apply_mem_smoothVectors_of_isSmooth v)
  left_inv g := by
    ext v
    simp
  right_inv f := by
    ext v
    simp

@[simp]
theorem IntertwiningMap.liftSmoothVectorsEquiv_apply {ρ : Representation A G V} [ρ.IsSmooth]
    {ρ' : Representation A G V'} (g : ρ.IntertwiningMap ρ'.smoothVectors.toRepresentation)
    (v : V) :
    IntertwiningMap.liftSmoothVectorsEquiv ρ' g v = (g v : V') := by
  simp [liftSmoothVectorsEquiv]

@[simp]
theorem IntertwiningMap.coe_liftSmoothVectorsEquiv_symm_apply {ρ : Representation A G V}
    [ρ.IsSmooth] {ρ' : Representation A G V'} (f : ρ.IntertwiningMap ρ') (v : V) :
    ((IntertwiningMap.liftSmoothVectorsEquiv ρ').symm f v : V') = f v := by
  simp [liftSmoothVectorsEquiv]

/-! ### Permutation and left regular representations -/

/-- A permutation representation `ofMulAction A G X` is smooth whenever every point of `X` has open
stabilizer in `G`. -/
theorem IsSmooth.ofMulAction_of_isOpen_stabilizer {X : Type*} [MulAction G X]
    (hX : ∀ x : X, IsOpen (MulAction.stabilizer G x : Set G)) :
    (ofMulAction A G X).IsSmooth := by
  rw [← smoothVectors_eq_top_iff, ← Subrepresentation.toSubmodule_injective.eq_iff,
    Subrepresentation.toSubmodule_top]
  suffices ∀ f : A[X], f ∈ (ofMulAction A G X).smoothVectors.toSubmodule from
    top_unique fun f _ ↦ this f
  intro f
  induction f using MonoidAlgebra.induction_linear with
  | zero => exact zero_mem _
  | add x y hx hy => exact add_mem hx hy
  | single x r =>
    exact Subgroup.isOpen_mono (le_stabilizer_ofMulAction_single x r) (hX x)

/-- Over a nontrivial coefficient semiring, the permutation representation `ofMulAction A G X` is
smooth if and only if every point of `X` has open stabilizer in `G`. -/
theorem isSmooth_ofMulAction_iff [Nontrivial A] {X : Type*} [MulAction G X] :
    (ofMulAction A G X).IsSmooth ↔ ∀ x : X, IsOpen (MulAction.stabilizer G x : Set G) := by
  refine ⟨fun h x ↦ ?_, IsSmooth.ofMulAction_of_isOpen_stabilizer⟩
  rw [← stabilizer_ofMulAction_single (A := A) x one_ne_zero]
  exact h.isOpen_stabilizer _

/-- For any open subgroup `U` of `G`, the permutation representation `A[G ⧸ U]` on the left coset
space is smooth. -/
instance IsSmooth.ofMulAction_quotient (U : OpenSubgroup G) :
    (ofMulAction A G (G ⧸ U.toSubgroup)).IsSmooth := by
  refine IsSmooth.ofMulAction_of_isOpen_stabilizer fun q ↦ ?_
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q
  have hstab : MulAction.stabilizer G (s : G ⧸ U.toSubgroup) =
      U.toSubgroup.map (MulAut.conj s) := by
    ext x
    simp only [TauCeti.stabilizer_quotientGroup_mk, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      MulAut.smul_def, MulAut.conj_inv_apply, Subgroup.mem_map, MonoidHom.coe_ofClass,
      MulAut.conj_apply]
    exact ⟨fun hx ↦ ⟨s⁻¹ * x * s, hx, by group⟩,
      by rintro ⟨y, hy, rfl⟩; simpa [mul_assoc] using hy⟩
  rw [hstab]
  exact isOpen_map_conj U.isOpen s

/-- In a non-discrete `T₁` group with separately continuous multiplication, the left regular
representation `A[G]` has no nonzero smooth vectors: `(leftRegular A G).smoothVectors = ⊥`. -/
theorem smoothVectors_leftRegular_eq_bot [T1Space G] (hG : ¬ DiscreteTopology G) :
    (leftRegular A G).smoothVectors = ⊥ := by
  rw [← Subrepresentation.toSubmodule_injective.eq_iff, Subrepresentation.toSubmodule_bot]
  ext f
  simp only [Subrepresentation.mem_toSubmodule, mem_smoothVectors, Submodule.mem_bot]
  refine ⟨fun hf ↦ ?_, fun hf ↦ by simp [hf, stabilizer_zero]⟩
  by_contra hne
  exact hG (OpenSubgroup.discreteTopology_of_finite ⟨_, hf⟩
    (finite_stabilizer_leftRegular_of_ne_zero hne))

/-- Over a nontrivial coefficient semiring, the left regular representation `A[G]` of a `T₁` group
with separately continuous multiplication is smooth if and only if `G` carries the discrete
topology. -/
theorem isSmooth_leftRegular_iff_discreteTopology [T1Space G] [Nontrivial A] :
    (leftRegular A G).IsSmooth ↔ DiscreteTopology G := by
  refine ⟨fun h ↦ ?_, fun _ ↦ inferInstance⟩
  by_contra hG
  have hbot : (leftRegular A G).smoothVectors = ⊥ := smoothVectors_leftRegular_eq_bot hG
  have htop : (leftRegular A G).smoothVectors = ⊤ := smoothVectors_eq_top _
  have h1 : (1 : A[G]) ∈ (⊥ : Submodule A A[G]) := by
    rw [← Subrepresentation.toSubmodule_bot (ρ := leftRegular A G), ← hbot, htop,
      Subrepresentation.toSubmodule_top]
    trivial
  simp at h1

end SeparatelyContinuousMul

/-! ### Invariant-subspace descriptions over a commutative ring -/

section Invariants

variable {A G V : Type*} [CommRing A] [Group G] [TopologicalSpace G]
  [AddCommGroup V] [Module A V]

section SeparatelyContinuousMul

variable [SeparatelyContinuousMul G]

/-- For any open subgroup `U` of `G`, the `U`-invariant vectors
`invariants (ρ.comp U.toSubgroup.subtype)` are smooth vectors. -/
theorem invariants_comp_openSubgroup_le_smoothVectors (ρ : Representation A G V)
    (U : OpenSubgroup G) :
    invariants (ρ.comp U.toSubgroup.subtype) ≤ ρ.smoothVectors.toSubmodule := by
  intro v hv
  rw [Subrepresentation.mem_toSubmodule, mem_smoothVectors_iff_exists_openSubgroup]
  exact ⟨U, fun g hg ↦ (mem_invariants (ρ.comp U.toSubgroup.subtype) v).mp hv ⟨g, hg⟩⟩

/-- A vector is smooth if and only if it lies in the `U`-invariants for some open subgroup `U`. -/
theorem mem_smoothVectors_iff_exists_mem_invariants_openSubgroup {ρ : Representation A G V}
    {v : V} :
    v ∈ ρ.smoothVectors ↔
      ∃ U : OpenSubgroup G, v ∈ invariants (ρ.comp U.toSubgroup.subtype) := by
  rw [mem_smoothVectors_iff_exists_openSubgroup]
  refine ⟨fun ⟨U, hU⟩ ↦ ⟨U, fun g ↦ hU g.1 g.2⟩,
    fun ⟨U, hU⟩ ↦ ⟨U, fun g hg ↦ hU ⟨g, hg⟩⟩⟩

/-- The submodule of smooth vectors is the supremum of the `U`-invariant submodules over all open
subgroups `U` of `G`. -/
theorem smoothVectors_toSubmodule_eq_iSup_invariants_openSubgroup (ρ : Representation A G V) :
    ρ.smoothVectors.toSubmodule =
      ⨆ U : OpenSubgroup G, invariants (ρ.comp U.toSubgroup.subtype) := by
  refine le_antisymm (fun v hv ↦ ?_) (iSup_le (ρ.invariants_comp_openSubgroup_le_smoothVectors))
  obtain ⟨U, hU⟩ := mem_smoothVectors_iff_exists_mem_invariants_openSubgroup.mp hv
  exact Submodule.mem_iSup_of_mem U hU

/-- As a set, the smooth vectors are the union of `V^U` over all open subgroups `U` of `G`. -/
theorem coe_smoothVectors_eq_iUnion_invariants_openSubgroup (ρ : Representation A G V) :
    (ρ.smoothVectors : Set V) =
      ⋃ U : OpenSubgroup G, (invariants (ρ.comp U.toSubgroup.subtype) : Set V) := by
  ext v
  simp only [SetLike.mem_coe, mem_iUnion,
    mem_smoothVectors_iff_exists_mem_invariants_openSubgroup]

end SeparatelyContinuousMul

section LocallyProfinite

variable [IsTopologicalGroup G] [WeaklyLocallyCompactSpace G] [ZeroDimensionalSpace G]

/-- In a weakly locally compact zero-dimensional topological group (in particular, any locally
profinite group), a vector is smooth if and only if it is fixed by some compact open subgroup. -/
theorem mem_smoothVectors_iff_exists_isCompact_openSubgroup {ρ : Representation A G V} {v : V} :
    v ∈ ρ.smoothVectors ↔
      ∃ U : OpenSubgroup G, IsCompact (U : Set G) ∧
        v ∈ invariants (ρ.comp U.toSubgroup.subtype) := by
  rw [mem_smoothVectors_iff_exists_mem_invariants_openSubgroup]
  refine ⟨fun ⟨W, hW⟩ ↦ ?_, fun ⟨U, _, hU⟩ ↦ ⟨U, hU⟩⟩
  obtain ⟨U, hUc, hUW⟩ := W.exists_isCompact_le
  exact ⟨U, hUc, fun g ↦ hW ⟨g.1, hUW g.2⟩⟩

/-- In a weakly locally compact zero-dimensional topological group, the submodule of smooth vectors
is the supremum of `V^U` over all compact open subgroups `U` of `G`. -/
theorem smoothVectors_toSubmodule_eq_iSup_invariants_isCompact (ρ : Representation A G V) :
    ρ.smoothVectors.toSubmodule =
      ⨆ (U : OpenSubgroup G) (_ : IsCompact (U : Set G)),
        invariants (ρ.comp U.toSubgroup.subtype) := by
  refine le_antisymm (fun v hv ↦ ?_)
    (iSup₂_le fun U _ ↦ ρ.invariants_comp_openSubgroup_le_smoothVectors U)
  obtain ⟨U, hUc, hU⟩ := mem_smoothVectors_iff_exists_isCompact_openSubgroup.mp hv
  exact Submodule.mem_iSup_of_mem U (Submodule.mem_iSup_of_mem hUc hU)

/-- In a weakly locally compact zero-dimensional topological group, the carrier of `V^∞` is the
set-theoretic union `⋃_U V^U` over all compact open subgroups `U` of `G`. -/
theorem coe_smoothVectors_eq_iUnion_invariants_isCompact (ρ : Representation A G V) :
    (ρ.smoothVectors : Set V) =
      ⋃ (U : OpenSubgroup G) (_ : IsCompact (U : Set G)),
        (invariants (ρ.comp U.toSubgroup.subtype) : Set V) := by
  ext v
  simp only [SetLike.mem_coe, mem_iUnion, exists_prop,
    mem_smoothVectors_iff_exists_isCompact_openSubgroup]

/-- In a weakly locally compact zero-dimensional topological group (in particular, any locally
profinite group), a representation is smooth if and only if every vector is fixed by some compact
open subgroup. -/
theorem isSmooth_iff_exists_isCompact_openSubgroup {ρ : Representation A G V} :
    ρ.IsSmooth ↔ ∀ v : V, ∃ U : OpenSubgroup G, IsCompact (U : Set G) ∧
      v ∈ invariants (ρ.comp U.toSubgroup.subtype) := by
  rw [← smoothVectors_eq_top_iff, ← Subrepresentation.toSubmodule_injective.eq_iff,
    Subrepresentation.toSubmodule_top, Submodule.eq_top_iff']
  simp only [Subrepresentation.mem_toSubmodule, mem_smoothVectors_iff_exists_isCompact_openSubgroup]

/-- In a weakly locally compact zero-dimensional topological group, `ρ` is smooth if and only if
the supremum of `V^U` over compact open subgroups `U` is `⊤`. -/
theorem isSmooth_iff_iSup_invariants_isCompact_eq_top {ρ : Representation A G V} :
    ρ.IsSmooth ↔
      (⨆ (U : OpenSubgroup G) (_ : IsCompact (U : Set G)),
        invariants (ρ.comp U.toSubgroup.subtype)) = ⊤ := by
  rw [← smoothVectors_eq_top_iff, ← Subrepresentation.toSubmodule_injective.eq_iff,
    Subrepresentation.toSubmodule_top, smoothVectors_toSubmodule_eq_iSup_invariants_isCompact]

/-- In a weakly locally compact zero-dimensional topological group, `ρ` is smooth if and only if
the union `⋃_U V^U` over compact open subgroups `U` exhausts `V`. -/
theorem isSmooth_iff_iUnion_invariants_isCompact_eq_univ {ρ : Representation A G V} :
    ρ.IsSmooth ↔
      (⋃ (U : OpenSubgroup G) (_ : IsCompact (U : Set G)),
        (invariants (ρ.comp U.toSubgroup.subtype) : Set V)) = Set.univ := by
  rw [isSmooth_iff_exists_isCompact_openSubgroup]
  simp [Set.eq_univ_iff_forall]

end LocallyProfinite

end Invariants

end Representation
