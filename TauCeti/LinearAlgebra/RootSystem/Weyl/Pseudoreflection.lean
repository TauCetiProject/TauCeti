/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.Basic
public import TauCeti.LinearAlgebra.RootSystem.Chamber
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Presentation
public import TauCeti.RepresentationTheory.ReflectingHyperplane
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.RootSystem.BaseExists
import Mathlib.LinearAlgebra.RootSystem.Reduced
import TauCeti.LinearAlgebra.Determinant.FiniteOrder

/-!
# Pseudoreflections and reflecting hyperplanes of the Weyl group

For a root pairing `P : RootPairing ι K M N` over a field `K` of characteristic not `2`, each root
reflection `weylGroup.ofIdx P i` fixes the coroot hyperplane `ker (P.coroot' i)` of codimension one,
so it is a pseudoreflection of `P.weylGroupRootRep` and
`P.weylGroupRootRep.pseudoreflectionSubgroup` is the whole Weyl group.

When `K` has characteristic zero and `P` is finite, reduced, and crystallographic, the converse
holds without assuming that `K` is ordered or that the roots span `M`: every pseudoreflection of
`P.weylGroupRootRep` is a root reflection `weylGroup.ofIdx P i`, and in fact is indexed uniquely by
a positive root `i ∈ posRoots P b` of any chosen base `b`. Consequently:

* every pseudoreflection of `P.weylGroupRootRep` is an involution, and agrees with a Coxeter
  reflection of `weylCoxeterSystem P b`;
* the pseudoreflections of `P.weylGroupRootRep` are in canonical bijection with `posRoots P b`, so
  there are `(posRoots P b).ncard = Nat.card ι / 2` of them;
* the reflecting hyperplanes `P.weylGroupRootRep.reflectingHyperplanes` are precisely the coroot
  hyperplanes `ker (P.coroot' i)` for `i ∈ posRoots P b`, each fixed pointwise inside `P.weylGroup`
  only by `1` and `weylGroup.ofIdx P i`;
* a weight is regular (`P.IsRegularWeight`) exactly when it lies on no reflecting hyperplane of
  `P.weylGroupRootRep`.

To prove that an arbitrary pseudoreflection `w ∈ P.weylGroup` is a root reflection without ordering
`K`, we first restrict `w` to the finite-dimensional root span `P.rootSpan K`: every generator acts
there as an involution, so the square of `(P.weylGroupRootRep w)|_(P.rootSpan K)` has determinant
`1`, fixes a hyperplane, and has finite order, hence is the identity by
`LinearMap.eq_one_of_det_eq_one_of_pow_eq_one`. Because the image of `w - 1` on `M` is
one-dimensional and already contains a nonzero vector of `P.rootSpan K` negated by `w`, `w` itself
is an involution on `M`. Conjugating `w` by a simple reflection in an inversion of `w` then either
strictly lowers the inversion count by two or exhibits a simple root negated by `w`, in which case
codimension one forces `w` to coincide with that simple reflection.

We also record that on a crystallographic root system (`[P.IsRootSystem]`), the characteristic
polynomial of `P.weylGroupRootRep w` comes by scalar extension from `ℤ[X]` (and hence from `ℚ[X]`),
since the simple roots of a base form a `K`-basis of `M` on which `w` acts with integer
coefficients.

## Main definitions

* `RootPairing.posRootsEquivPseudoreflections`: the bijection `posRoots P b ≃` pseudoreflections of
  `P.weylGroupRootRep`, sending `i` to `weylGroup.ofIdx P i`.
* `RootPairing.posRootsEquivReflectingHyperplanes`: the bijection `posRoots P b ≃`
  `P.weylGroupRootRep.reflectingHyperplanes`, sending `i` to `LinearMap.ker (P.coroot' i)`.

## Main results

* `RootPairing.weylGroupRootRep_injective` and `RootPairing.ker_weylGroupRootRep`: faithfulness of
  `P.weylGroupRootRep`.
* `RootPairing.finite_weight_of_isRootSystem`: finite generation of the weight module of a finite
  root system.
* `RootPairing.exists_map_int_eq_charpoly_weylGroupRootRep_of_base` and
  `RootPairing.exists_map_int_eq_charpoly_weylGroupRootRep`: integrality of characteristic
  polynomials on a crystallographic root system.
* `RootPairing.fixedSubmodule_weylGroupRootRep_ofIdx`,
  `RootPairing.finrank_quotient_fixedSubmodule_weylGroupRootRep_ofIdx`, and
  `RootPairing.pseudoreflectionSubgroup_weylGroupRootRep`: each `ofIdx P i` has fixed hyperplane
  `ker (P.coroot' i)` of codimension one, and the pseudoreflections generate `P.weylGroup`.
* `RootPairing.weylGroup.mul_self_eq_one_of_finrank_quotient_fixedSubmodule_eq_one`: every
  pseudoreflection in `P.weylGroup` is an involution.
* `RootPairing.finrank_quotient_fixedSubmodule_weylGroupRootRep_eq_one_iff_of_base`,
  `RootPairing.finrank_quotient_fixedSubmodule_weylGroupRootRep_eq_one_iff`, and
  `RootPairing.weylCoxeterSystem_isReflection_iff_finrank_quotient_fixedSubmodule_eq_one`: the
  pseudoreflections of `P.weylGroupRootRep` are precisely the root reflections (and the Coxeter
  reflections).
* `RootPairing.mem_reflectingHyperplanes_weylGroupRootRep_iff_exists_mem_posRoots` and
  `RootPairing.ker_coroot'_le_fixedSubmodule_weylGroupRootRep_iff`: the reflecting hyperplanes and
  their two-element pointwise stabilizers `{1, weylGroup.ofIdx P i}`.
* `RootPairing.isRegularWeight_iff_forall_notMem_reflectingHyperplanes_of_base` and
  `RootPairing.isRegularWeight_iff_forall_notMem_reflectingHyperplanes`: regular weights are the
  complement of the reflecting-hyperplane arrangement.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Chapter V, §2, and Chapter VI, §1.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge Studies in Advanced
  Mathematics 29, Cambridge University Press (1990), §§1.14, 3.1, 3.9.
* R. Kane, *Reflection Groups and Invariant Theory*, CMS Books in Mathematics, Springer (2001),
  §18.
-/

public section

open Module Set TauCeti

namespace RootPairing

section CommRing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (P : RootPairing ι R M N)

/-- The weight-space representation of the Weyl group acts by scalar multiplication. -/
@[simp]
theorem weylGroupRootRep_apply (w : P.weylGroup) (x : M) :
    P.weylGroupRootRep w x = w • x :=
  rfl

/-- On the weight space, the Weyl-group generator `weylGroup.ofIdx P i` acts as `P.reflection i`. -/
theorem weylGroupRootRep_ofIdx_apply (i : ι) (x : M) :
    P.weylGroupRootRep (weylGroup.ofIdx P i) x = P.reflection i x :=
  rfl

/-- The weight-space representation of the Weyl group is faithful, without any spanning
hypothesis on the roots. -/
theorem weylGroupRootRep_injective : Function.Injective P.weylGroupRootRep :=
  fun _ _ h ↦ weylGroup.ext (LinearMap.congr_fun h)

/-- The kernel of `P.weylGroupRootRep` is trivial. -/
@[simp]
theorem ker_weylGroupRootRep : P.weylGroupRootRep.ker = ⊥ :=
  eq_bot_iff.mpr fun _ hw ↦ P.weylGroupRootRep_injective (by simpa using hw)

/-- On a finite root system, the weight module is finitely generated because it is spanned by the
finite set of roots. -/
theorem finite_weight_of_isRootSystem [Finite ι] [P.IsRootSystem] : Module.Finite R M :=
  Module.finite_def.mpr
    (IsRootSystem.span_root_eq_top (P := P) ▸ Submodule.fg_span (Set.finite_range P.root))

/-- Reflecting a root index across itself does not change the associated Weyl-group reflection. -/
@[simp]
theorem weylGroup.ofIdx_reflectionPerm_self (i : ι) :
    weylGroup.ofIdx P (P.reflectionPerm i i) = weylGroup.ofIdx P i := by
  ext x
  change P.reflection (P.reflectionPerm i i) x = P.reflection i x
  rw [reflection_apply, reflection_apply, root_reflectionPerm, coroot'_reflectionPerm_self,
    reflection_apply_self]
  simp

/-- The Weyl-group reflection attached to the negative of a root index is the same reflection. -/
theorem weylGroup.ofIdx_neg (i : ι) :
    letI := P.indexNeg
    weylGroup.ofIdx P (-i) = weylGroup.ofIdx P i := by
  let := P.indexNeg
  simp

/-- Over an integral domain where `2` is nonzero and `M` is torsion-free, the fixed submodule of
the reflection in `i` is the kernel of the coroot functional `P.coroot' i`. -/
@[simp]
theorem fixedSubmodule_weylGroupRootRep_ofIdx [IsDomain R] [IsTorsionFree R M] [NeZero (2 : R)]
    (i : ι) :
    (P.weylGroupRootRep (weylGroup.ofIdx P i)).fixedSubmodule = LinearMap.ker (P.coroot' i) := by
  ext x
  rw [LinearMap.mem_fixedSubmodule_iff, weylGroupRootRep_ofIdx_apply, reflection_apply,
    sub_eq_self, smul_eq_zero, LinearMap.mem_ker]
  exact or_iff_left (P.ne_zero i)

/-- **Coxeter reflections of a Weyl group are precisely the root reflections.** Every conjugate of
a simple reflection is the reflection in the transported simple root, and conversely every root is
in the Weyl orbit of a simple root. -/
theorem weylCoxeterSystem_isReflection_iff_exists_ofIdx [Finite ι] [CharZero R] [IsDomain R]
    [P.IsCrystallographic] [P.IsReduced] (b : P.Base) {w : P.weylGroup} :
    (weylCoxeterSystem P b).IsReflection w ↔ ∃ i : ι, w = weylGroup.ofIdx P i := by
  refine ⟨?_, fun ⟨i, hi⟩ ↦ hi ▸ P.weylCoxeterSystem_isReflection_ofIdx b i⟩
  rintro ⟨u, j, rfl⟩
  exact ⟨P.weylGroupToPerm u j, by
    rw [weylCoxeterSystem_simple, weylGroup.ofIdx_weylGroupToPerm_eq_conj]⟩

/-- On a root system with a base `b`, the characteristic polynomial of any Weyl-group element on
`M` is the scalar extension of an integer polynomial: the simple roots form an `R`-basis
`b.toWeightBasis` of `M`, and `w` expands each simple root as an integer combination of simple
roots. -/
theorem exists_map_int_eq_charpoly_weylGroupRootRep_of_base [CharZero R] [Module.Free R M]
    [Module.Finite R M] [P.IsRootSystem] (b : P.Base) (w : P.weylGroup) :
    ∃ p : Polynomial ℤ, p.map (algebraMap ℤ R) = (P.weylGroupRootRep w).charpoly := by
  classical
  choose c _ _ hc using fun j : b.support ↦ b.exists_root_eq_sum_int (P.weylGroupToPerm w j)
  let A : Matrix b.support b.support ℤ := fun i j ↦ c j i
  have hmat : LinearMap.toMatrix b.toWeightBasis b.toWeightBasis (P.weylGroupRootRep w) =
      A.map (algebraMap ℤ R) := by
    ext i j
    have hw : P.weylGroupRootRep w (b.toWeightBasis j) =
        ∑ k : b.support, (algebraMap ℤ R (A k j)) • b.toWeightBasis k := by
      rw [weylGroupRootRep_apply, Base.toWeightBasis_apply, P.weylGroup_apply_root, hc j,
        ← Finset.sum_attach b.support]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [Base.toWeightBasis_apply, eq_intCast, Int.cast_smul_eq_zsmul]
    rw [LinearMap.toMatrix_apply, ← Basis.equivFun_apply, hw, map_sum, Finset.sum_apply]
    simp [A, Finsupp.single_apply]
    rfl
  refine ⟨A.charpoly, ?_⟩
  rw [← (P.weylGroupRootRep w).charpoly_toMatrix b.toWeightBasis, hmat, Matrix.charpoly_map]

/-- On a root system with a base over a `ℚ`-algebra of characteristic zero, the characteristic
polynomial of any Weyl-group element on `M` is the scalar extension of a rational polynomial. -/
theorem exists_map_rat_eq_charpoly_weylGroupRootRep_of_base [CharZero R] [Algebra ℚ R]
    [Module.Free R M] [Module.Finite R M] [P.IsRootSystem] (b : P.Base) (w : P.weylGroup) :
    ∃ p : Polynomial ℚ, p.map (algebraMap ℚ R) = (P.weylGroupRootRep w).charpoly := by
  obtain ⟨p, hp⟩ := P.exists_map_int_eq_charpoly_weylGroupRootRep_of_base b w
  refine ⟨p.map (algebraMap ℤ ℚ), ?_⟩
  rwa [Polynomial.map_map,
    Subsingleton.elim ((algebraMap ℚ R).comp (algebraMap ℤ ℚ)) (algebraMap ℤ R)]

end CommRing

section Field

variable {ι K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N] (P : RootPairing ι K M N)

section NeZeroTwo

variable [NeZero (2 : K)]

/-- Over a field of characteristic not `2`, every root reflection has a codimension-one fixed
subspace. Neither finite-dimensionality of `M` nor finiteness of `ι` is required. -/
@[simp]
theorem finrank_quotient_fixedSubmodule_weylGroupRootRep_ofIdx (i : ι) :
    finrank K (M ⧸ (P.weylGroupRootRep (weylGroup.ofIdx P i)).fixedSubmodule) = 1 := by
  rw [P.fixedSubmodule_weylGroupRootRep_ofIdx,
    (P.coroot' i).finrank_quotient_ker_eq_one_of_ne_zero (P.coroot'_ne_zero i)]

/-- Every root reflection belongs to the pseudoreflection subgroup of `P.weylGroupRootRep`. -/
theorem ofIdx_mem_pseudoreflectionSubgroup_weylGroupRootRep (i : ι) :
    weylGroup.ofIdx P i ∈ P.weylGroupRootRep.pseudoreflectionSubgroup :=
  P.weylGroupRootRep.mem_pseudoreflectionSubgroup_of_finrank_quotient_eq_one
    (P.finrank_quotient_fixedSubmodule_weylGroupRootRep_ofIdx i)

/-- Over any field of characteristic not `2`, the Weyl group is generated by the pseudoreflections
of its weight-space representation. -/
@[simp]
theorem pseudoreflectionSubgroup_weylGroupRootRep :
    P.weylGroupRootRep.pseudoreflectionSubgroup = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨w, hw⟩ -
  induction hw using weylGroup.induction with
  | mem i => exact P.ofIdx_mem_pseudoreflectionSubgroup_weylGroupRootRep i
  | one => exact one_mem _
  | mul x y hx hy ihx ihy =>
    exact (Submonoid.mk_mul_mk P.weylGroup.toSubmonoid x y hx hy) ▸ mul_mem ihx ihy

/-- Over any field of characteristic not `2`, the Weyl group is also generated by the
pseudoreflections of the contragredient representation `P.weylGroupRootRep.dual`. -/
@[simp]
theorem pseudoreflectionSubgroup_weylGroupRootRep_dual :
    P.weylGroupRootRep.dual.pseudoreflectionSubgroup = ⊤ := by
  rw [Representation.pseudoreflectionSubgroup_def]
  simp_rw [P.weylGroupRootRep.finrank_quotient_fixedSubmodule_dual]
  rw [← Representation.pseudoreflectionSubgroup_def]
  exact P.pseudoreflectionSubgroup_weylGroupRootRep

end NeZeroTwo

section PosRootsUniqueness

variable [CharZero K] [P.IsReduced]

/-- Distinct positive roots of a base yield distinct reflections in the Weyl group, without any
finiteness hypothesis on `ι`. -/
theorem ofIdx_injOn_posRoots (b : P.Base) :
    InjOn (weylGroup.ofIdx P) (posRoots P b) := by
  intro i hi j hj h
  refine eq_of_isPos_of_reflection_eq ((mem_posRoots P b i).mp hi) ((mem_posRoots P b j).mp hj)
    (congrArg (fun w ↦ P.weylGroupRootRep w (P.root i)) h) ?_
  rw [reflection_apply_self]
  intro hneg
  have h2 : (2 : K) • P.root i = 0 := by
    rw [two_smul]
    exact add_eq_zero_iff_eq_neg.mpr hneg.symm
  exact P.ne_zero i ((smul_eq_zero.mp h2).resolve_left two_ne_zero)

/-- In a finite reduced root pairing over a field of characteristic zero, distinct positive roots
of a base cut out distinct coroot hyperplanes. -/
theorem ker_coroot'_injOn_posRoots [Finite ι] (b : P.Base) :
    InjOn (fun i ↦ LinearMap.ker (P.coroot' i)) (posRoots P b) := by
  intro i hi j hj hker
  dsimp only at hker
  have hrel (x : M) : P.coroot' j x =
      ((2 : K)⁻¹ * P.coroot' j (P.root i)) * P.coroot' i x := by
    have hx : x - ((2 : K)⁻¹ * P.coroot' i x) • P.root i ∈ LinearMap.ker (P.coroot' i) := by
      rw [LinearMap.mem_ker, map_sub, map_smul, root_coroot'_eq_pairing, pairing_same, smul_eq_mul]
      ring_nf
    rw [hker, LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, sub_eq_zero] at hx
    rw [hx]
    ring
  set c : K := (2 : K)⁻¹ * P.coroot' j (P.root i)
  have hcoroot' : P.coroot' j = c • P.coroot' i := LinearMap.ext hrel
  have hcoroot : P.coroot j = c • P.coroot i :=
    P.toLinearMap.flip.toPerfPair.injective <| by
      change P.coroot' j = P.toLinearMap.flip.toPerfPair (c • P.coroot i)
      rw [map_smul]
      exact hcoroot'
  have hdep : ¬ LinearIndependent K ![P.flip.root j, P.flip.root i] := by
    rw [LinearIndependent.pair_iff]
    intro hli
    have h0 := hli (-1) c (by simp [hcoroot])
    norm_num at h0
  rcases IsReduced.eq_or_eq_neg (P := P.flip) j i hdep with heq | hneg
  · exact (P.coroot.injective heq).symm
  · exfalso
    have hjneg : j = P.reflectionPerm i i := P.coroot.injective <| by
      rw [coroot_reflectionPerm, coreflection_apply_self]
      exact hneg
    exact reflectionPerm_self_notMem_posRoots P b hi (hjneg ▸ hj)

end PosRootsUniqueness

/-- Every Weyl-group element preserves the `K`-span of the roots. -/
private theorem weylGroupRootRep_mem_rootSpan (w : P.weylGroup) (x : M) (hx : x ∈ P.rootSpan K) :
    P.weylGroupRootRep w x ∈ P.rootSpan K := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    rw [weylGroupRootRep_apply, P.weylGroup_apply_root]
    exact Submodule.subset_span ⟨P.weylGroupToPerm w i, rfl⟩
  | zero =>
    rw [map_zero]
    exact zero_mem _
  | add y z _ _ hy hz =>
    rw [map_add]
    exact add_mem hy hz
  | smul c y _ hy =>
    rw [map_smul]
    exact Submodule.smul_mem _ c hy

/-- The restriction of `P.weylGroupRootRep` to the root span `P.rootSpan K`. -/
private noncomputable def weylGroupRootSpanRep : Representation K P.weylGroup (P.rootSpan K) where
  toFun w := (P.weylGroupRootRep w).restrict (P.weylGroupRootRep_mem_rootSpan w)
  map_one' := by ext; simp
  map_mul' u v := by ext; simp

/-- Every Weyl-group element acts on `P.rootSpan K` with determinant `±1` (its square is `1`). -/
private theorem det_weylGroupRootSpanRep_sq (w : P.weylGroup) :
    LinearMap.det (P.weylGroupRootSpanRep w) ^ 2 = 1 := by
  obtain ⟨g, hg⟩ := w
  induction hg using weylGroup.induction with
  | mem i =>
    change LinearMap.det (P.weylGroupRootSpanRep (weylGroup.ofIdx P i)) ^ 2 = 1
    have hsq : P.weylGroupRootSpanRep (weylGroup.ofIdx P i) ^ 2 = 1 := by
      rw [sq, ← map_mul, weylGroup.ofIdx_mul_self, map_one]
    rw [← map_pow, hsq, map_one]
  | one =>
    change LinearMap.det (P.weylGroupRootSpanRep 1) ^ 2 = 1
    rw [map_one, map_one, one_pow]
  | mul x y hx hy ihx ihy =>
    change LinearMap.det (P.weylGroupRootSpanRep (⟨x, hx⟩ * ⟨y, hy⟩)) ^ 2 = 1
    rw [map_mul, map_mul, mul_pow, ihx, ihy, mul_one]

section Classification

variable [CharZero K] [Finite ι] [P.IsCrystallographic] [P.IsReduced]

/-- **Every pseudoreflection in the Weyl group is an involution.** Even over an unordered field
such as `ℂ` and without assuming `M` is spanned by the roots or finite-dimensional, an element of
`P.weylGroup` whose fixed space has codimension one in `M` has order two. -/
theorem weylGroup.mul_self_eq_one_of_finrank_quotient_fixedSubmodule_eq_one (b : P.Base)
    {w : P.weylGroup} (hw : finrank K (M ⧸ (P.weylGroupRootRep w).fixedSubmodule) = 1) :
    w * w = 1 := by
  have : Finite P.weylGroup := P.finite_weylGroup_of_base b
  have : Module.Finite K (P.rootSpan K) :=
    Module.Finite.span_of_finite K (Set.finite_range P.root)
  set f : M →ₗ[K] M := P.weylGroupRootRep w
  set fS : P.rootSpan K →ₗ[K] P.rootSpan K := P.weylGroupRootSpanRep w
  have hw1 : w ≠ 1 := P.weylGroupRootRep.ne_one_of_finrank_quotient_fixedSubmodule_eq_one hw
  obtain ⟨i₀, hi₀⟩ := inversions_nonempty_of_ne_one (b := b) hw1
  rw [mem_inversions] at hi₀
  have hmove : w • P.root i₀ ≠ P.root i₀ := by
    intro hfix
    rw [P.weylGroup_apply_root] at hfix
    rw [P.root.injective hfix] at hi₀
    exact hi₀.2 hi₀.1
  set u : M := w • P.root i₀ - P.root i₀
  have hu0 : u ≠ 0 := sub_ne_zero.mpr hmove
  -- The quotient of `P.rootSpan K` by `fS.fixedSubmodule` injects into `M ⧸ f.fixedSubmodule`,
  -- and is nontrivial because `P.root i₀` is moved, so its `finrank` is `1`.
  have hcomap : fS.fixedSubmodule = f.fixedSubmodule.comap (P.rootSpan K).subtype :=
    LinearMap.fixedSubmodule_restrict (P.weylGroupRootRep_mem_rootSpan w)
  let qMap : (P.rootSpan K ⧸ fS.fixedSubmodule) →ₗ[K] M ⧸ f.fixedSubmodule :=
    Submodule.mapQ fS.fixedSubmodule f.fixedSubmodule (P.rootSpan K).subtype
      (by rw [hcomap])
  have hfin_le : finrank K (P.rootSpan K ⧸ fS.fixedSubmodule) ≤ 1 := by
    have hker : LinearMap.ker qMap = ⊥ := by
      rw [Submodule.ker_mapQ, ← hcomap, Submodule.mkQ_map_self]
    have : FiniteDimensional K (M ⧸ f.fixedSubmodule) :=
      Module.finite_of_finrank_pos (by omega)
    exact (LinearMap.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp hker)).trans hw.le
  have hfin_ne : finrank K (P.rootSpan K ⧸ fS.fixedSubmodule) ≠ 0 := by
    intro h0
    have hsub := Module.finrank_zero_iff.mp h0
    have hmem : (⟨P.root i₀, Submodule.subset_span ⟨i₀, rfl⟩⟩ : P.rootSpan K) ∈
        fS.fixedSubmodule := by
      rw [← Submodule.Quotient.mk_eq_zero]
      exact Subsingleton.elim _ _
    rw [LinearMap.mem_fixedSubmodule_iff, Subtype.ext_iff] at hmem
    exact hmove hmem
  have hfinS : finrank K (P.rootSpan K ⧸ fS.fixedSubmodule) = 1 := by omega
  -- Apply the finite-order determinant lemma to `fS ^ 2` on `P.rootSpan K`.
  have hfS_sq : fS ^ 2 = 1 := by
    apply (fS ^ 2).eq_one_of_det_eq_one_of_pow_eq_one fS.fixedSubmodule hfinS
    · exact fun x hx ↦ fS.pow_apply_of_mem_fixedSubmodule hx 2
    · rw [map_pow, P.det_weylGroupRootSpanRep_sq w]
    · exact Nat.cast_ne_zero.mpr (Nat.card_pos (α := P.weylGroup)).ne'
    · rw [← pow_mul, mul_comm, pow_mul, ← map_pow (P.weylGroupRootSpanRep),
        pow_card_eq_one' (x := w), map_one, one_pow]
  -- Hence `w` negates `u`, and since `range (f - 1)` is spanned by `u`, `w * w = 1` on all of `M`.
  have hfu : w • u = -u := by
    let r₀ : P.rootSpan K := ⟨P.root i₀, Submodule.subset_span ⟨i₀, rfl⟩⟩
    have h1 : (fS ^ 2) r₀ = r₀ := LinearMap.congr_fun hfS_sq r₀
    have h2 : ((fS ^ 2) r₀ : M) = w • (w • P.root i₀) := by
      simp [sq, fS, weylGroupRootSpanRep, r₀]
    have hww : w • (w • P.root i₀) = P.root i₀ := by
      simpa [r₀] using congrArg Subtype.val h1 |>.symm.trans h2 |>.symm
    simp only [u, smul_sub, hww]
    abel
  have hrange_fin : finrank K (LinearMap.range (f - LinearMap.id)) = 1 := by
    rw [← LinearEquiv.finrank_eq (f - LinearMap.id).quotKerEquivRange,
      ← LinearMap.fixedSubmodule_eq_ker]
    exact hw
  have hu_mem : u ∈ LinearMap.range (f - LinearMap.id) := ⟨P.root i₀, rfl⟩
  have hspan : K ∙ (⟨u, hu_mem⟩ : LinearMap.range (f - LinearMap.id)) = ⊤ := by
    have : FiniteDimensional K (LinearMap.range (f - LinearMap.id)) :=
      Module.finite_of_finrank_pos (by omega)
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_singleton (mt (congrArg Subtype.val) hu0), hrange_fin]
  ext x
  have hx_mem : (⟨w • x - x, ⟨x, rfl⟩⟩ : LinearMap.range (f - LinearMap.id)) ∈
      (⊤ : Submodule K (LinearMap.range (f - LinearMap.id))) := Submodule.mem_top
  rw [← hspan, Submodule.mem_span_singleton] at hx_mem
  obtain ⟨c, hc⟩ := hx_mem
  have hwx : w • x = x + c • u := eq_add_of_sub_eq' (congrArg Subtype.val hc).symm
  rw [mul_smul, hwx, smul_add, hwx, smul_comm w c u, hfu, smul_neg, one_smul]
  abel

omit [Finite ι] [P.IsCrystallographic] [P.IsReduced] in
/-- If an element `w` of `P.weylGroup` fixes a hyperplane and negates the root `i`, then
`w = weylGroup.ofIdx P i`. -/
private theorem eq_ofIdx_of_finrank_quotient_fixedSubmodule_eq_one_of_weylGroupToPerm_eq_neg
    {w : P.weylGroup} (hw : finrank K (M ⧸ (P.weylGroupRootRep w).fixedSubmodule) = 1)
    {i : ι} (hi : P.weylGroupToPerm w i = P.reflectionPerm i i) :
    w = weylGroup.ofIdx P i := by
  have hle : (P.weylGroupRootRep w).fixedSubmodule ≤ LinearMap.ker (P.coroot' i) := by
    intro x hx
    rw [LinearMap.mem_fixedSubmodule_iff, weylGroupRootRep_apply] at hx
    rw [LinearMap.mem_ker]
    have hcor : P.coroot' i x = -P.coroot' i x := by
      calc
        P.coroot' i x = P.coroot' (P.weylGroupToPerm w i) (w • x) :=
          (P.coroot'_weylGroupToPerm_smul w i x).symm
        _ = P.coroot' (P.reflectionPerm i i) x := by rw [hi, hx]
        _ = -P.coroot' i x := P.coroot'_reflectionPerm_self i ▸ rfl
    exact CharZero.eq_neg_self_iff.mp hcor
  have hker_fin : finrank K (M ⧸ LinearMap.ker (P.coroot' i)) = 1 :=
    (P.coroot' i).finrank_quotient_ker_eq_one_of_ne_zero (P.coroot'_ne_zero i)
  have : FiniteDimensional K (M ⧸ (P.weylGroupRootRep w).fixedSubmodule) :=
    Module.finite_of_finrank_pos (by omega)
  have : FiniteDimensional K (M ⧸ LinearMap.ker (P.coroot' i)) :=
    Module.finite_of_finrank_pos (by omega)
  have hinj : Function.Injective (Submodule.factor hle) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hw.trans hker_fin.symm)).mpr
      (Submodule.factor_surjective hle)
  have hfixed : (P.weylGroupRootRep w).fixedSubmodule = LinearMap.ker (P.coroot' i) :=
    hle.antisymm fun z hz ↦ by
      rw [← Submodule.Quotient.mk_eq_zero] at hz ⊢
      exact hinj <| by
        rw [← Submodule.mkQ_apply, Submodule.factor_mk, Submodule.mkQ_apply, hz, map_zero]
  refine weylGroup.ext fun x ↦ ?_
  set y : M := x - ((2 : K)⁻¹ * P.coroot' i x) • P.root i
  have hy_ker : y ∈ LinearMap.ker (P.coroot' i) := by
    rw [LinearMap.mem_ker, map_sub, map_smul, root_coroot'_eq_pairing, pairing_same, smul_eq_mul]
    ring_nf
  have hwy : w • y = y := by
    rw [← weylGroupRootRep_apply, ← LinearMap.mem_fixedSubmodule_iff, hfixed]
    exact hy_ker
  have hsy : weylGroup.ofIdx P i • y = y := by
    rw [← weylGroupRootRep_apply, ← LinearMap.mem_fixedSubmodule_iff,
      P.fixedSubmodule_weylGroupRootRep_ofIdx]
    exact hy_ker
  have hwroot : w • P.root i = -P.root i := by
    rw [P.weylGroup_apply_root, hi, root_reflectionPerm, reflection_apply_self]
  have hsroot : weylGroup.ofIdx P i • P.root i = -P.root i := by
    rw [weylGroup.ofIdx_smul, Equiv.reflection_smul, reflection_apply_self]
  have hx_decomp : x = y + ((2 : K)⁻¹ * P.coroot' i x) • P.root i := by simp [y]
  rw [hx_decomp, smul_add, smul_add, hwy, hsy, smul_comm w, smul_comm (weylGroup.ofIdx P i),
    hwroot, hsroot]

/-- Strong induction on the number of inversions showing that every pseudoreflection of
`P.weylGroupRootRep` is a root reflection `weylGroup.ofIdx P k`. -/
private theorem exists_ofIdx_of_finrank_quotient_fixedSubmodule_eq_one_aux (b : P.Base) :
    ∀ n : ℕ, ∀ w : P.weylGroup, (inversions P b w).ncard = n →
      finrank K (M ⧸ (P.weylGroupRootRep w).fixedSubmodule) = 1 →
      ∃ k : ι, w = weylGroup.ofIdx P k := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro w hn hw
    have hw1 : w ≠ 1 := P.weylGroupRootRep.ne_one_of_finrank_quotient_fixedSubmodule_eq_one hw
    obtain ⟨i, hi_supp, hi_inv⟩ := exists_mem_support_mem_inversions_of_ne_one P b hw1
    by_cases hneg : P.weylGroupToPerm w i = P.reflectionPerm i i
    · exact ⟨i,
        P.eq_ofIdx_of_finrank_quotient_fixedSubmodule_eq_one_of_weylGroupToPerm_eq_neg hw hneg⟩
    · set s : P.weylGroup := weylGroup.ofIdx P i
      have hwinv : w⁻¹ = w :=
        inv_eq_iff_mul_eq_one.mpr
          (weylGroup.mul_self_eq_one_of_finrank_quotient_fixedSubmodule_eq_one P b hw)
      have hsinv : s⁻¹ = s := weylGroup.ofIdx_inv_eq P i
      -- Since `w i` is negative and not `-i`, `s` keeps `w i` negative, so `i` is an inversion of
      -- `(w * s)⁻¹ = s * w` and conjugating `w` by `s` drops the inversion count by two.
      have hwi_neg : P.weylGroupToPerm w i ∈ negRoots P b :=
        mapsTo_inversions_negRoots P b w hi_inv
      have hpos_neg : P.reflectionPerm (P.weylGroupToPerm w i) (P.weylGroupToPerm w i) ∈
          posRoots P b \ {i} := by
        refine ⟨(reflectionPerm_self_mem_posRoots_iff_mem_negRoots P b _).mpr hwi_neg, ?_⟩
        intro hcon
        apply hneg
        rw [Set.mem_singleton_iff] at hcon
        simpa using congrArg (fun k ↦ P.reflectionPerm k k) hcon
      have hs_neg : ¬ b.IsPos (P.weylGroupToPerm (s * w) i) := by
        let := P.indexNeg
        rw [weylGroupToPerm_ofIdx_mul_apply]
        have hpos_i : P.reflectionPerm i
            (P.reflectionPerm (P.weylGroupToPerm w i) (P.weylGroupToPerm w i)) ∈
            posRoots P b \ {i} :=
          ((reflectionPerm_mem_posRoots_diff_singleton_iff P b hi_supp _).mpr hpos_neg)
        have hcomm : P.reflectionPerm i (P.weylGroupToPerm w i) =
            -(P.reflectionPerm i (-P.weylGroupToPerm w i)) := by
          symm
          rw [← weylGroupToPerm_ofIdx_apply, P.weylGroupToPerm_neg, neg_neg,
            weylGroupToPerm_ofIdx_apply]
        rw [← indexNeg_neg] at hpos_i
        rw [hcomm, Base.IsPos.neg_iff_not]
        exact not_not.mpr ((mem_posRoots P b _).mp hpos_i.1)
      have hi_inv_sw : i ∈ inversions P b (w * s)⁻¹ := by
        rw [mul_inv_rev, hsinv, hwinv, mem_inversions]
        exact ⟨b.isPos_of_mem_support hi_supp, hs_neg⟩
      have hlt1 : (inversions P b (s * (w * s))).ncard < (inversions P b (w * s)).ncard :=
        (ncard_inversions_ofIdx_mul_lt_iff P b (w * s) (b.isPos_of_mem_support hi_supp)).mpr
          hi_inv_sw
      have hlt2 : (inversions P b (w * s)).ncard < (inversions P b w).ncard :=
        ncard_inversions_mul_ofIdx_lt_of_mem P b w hi_inv
      have hlt : (inversions P b (s * w * s)).ncard < n := by
        rw [mul_assoc]
        exact hlt1.trans (hlt2.trans_eq hn)
      have hw_conj : finrank K (M ⧸ (P.weylGroupRootRep (s * w * s)).fixedSubmodule) = 1 := by
        have hconj := P.weylGroupRootRep.finrank_quotient_fixedSubmodule_conj s w
        rwa [hsinv, hw] at hconj
      obtain ⟨k, hk⟩ := ih _ hlt (s * w * s) rfl hw_conj
      refine ⟨P.weylGroupToPerm s k, ?_⟩
      rw [weylGroup.ofIdx_weylGroupToPerm_eq_conj, hsinv, ← hk]
      dsimp only [s]
      rw [← mul_assoc, ← mul_assoc, weylGroup.ofIdx_mul_self, one_mul, mul_assoc,
        weylGroup.ofIdx_mul_self, mul_one]

/-- **Classification of the pseudoreflections of `P.weylGroupRootRep`.** Relative to a base `b`
(without assuming that `M` is finite-dimensional or spanned by the roots), an element of the Weyl
group fixes a hyperplane in `M` if and only if it is a root reflection `weylGroup.ofIdx P i`. -/
theorem finrank_quotient_fixedSubmodule_weylGroupRootRep_eq_one_iff_of_base (b : P.Base)
    {w : P.weylGroup} :
    finrank K (M ⧸ (P.weylGroupRootRep w).fixedSubmodule) = 1 ↔
      ∃ i : ι, w = weylGroup.ofIdx P i :=
  ⟨P.exists_ofIdx_of_finrank_quotient_fixedSubmodule_eq_one_aux b _ w rfl,
    fun ⟨i, hi⟩ ↦ hi ▸ P.finrank_quotient_fixedSubmodule_weylGroupRootRep_ofIdx i⟩

/-- Every pseudoreflection of `P.weylGroupRootRep` is the reflection in a positive root of `b`. -/
theorem finrank_quotient_fixedSubmodule_weylGroupRootRep_eq_one_iff_exists_mem_posRoots
    (b : P.Base) {w : P.weylGroup} :
    finrank K (M ⧸ (P.weylGroupRootRep w).fixedSubmodule) = 1 ↔
      ∃ i ∈ posRoots P b, w = weylGroup.ofIdx P i := by
  rw [P.finrank_quotient_fixedSubmodule_weylGroupRootRep_eq_one_iff_of_base b]
  refine ⟨?_, fun ⟨i, _, hi⟩ ↦ ⟨i, hi⟩⟩
  rintro ⟨i, rfl⟩
  by_cases hi : b.IsPos i
  · exact ⟨i, (mem_posRoots P b i).mpr hi, rfl⟩
  · let := P.indexNeg
    exact ⟨-i, (mem_posRoots P b (-i)).mpr ((Base.IsPos.neg_iff_not b i).mpr hi),
      (weylGroup.ofIdx_neg P i).symm⟩

/-- **Coxeter reflections agree with geometric pseudoreflections.** An element of `P.weylGroup` is
a reflection of the Coxeter system `weylCoxeterSystem P b` if and only if its fixed space on `M`
has codimension one. -/
theorem weylCoxeterSystem_isReflection_iff_finrank_quotient_fixedSubmodule_eq_one (b : P.Base)
    {w : P.weylGroup} :
    (weylCoxeterSystem P b).IsReflection w ↔
      finrank K (M ⧸ (P.weylGroupRootRep w).fixedSubmodule) = 1 :=
  (P.weylCoxeterSystem_isReflection_iff_exists_ofIdx b).trans
    (P.finrank_quotient_fixedSubmodule_weylGroupRootRep_eq_one_iff_of_base b).symm

/-- **Bijection between the positive roots of a base and the pseudoreflections of
`P.weylGroupRootRep`.** -/
noncomputable def posRootsEquivPseudoreflections (b : P.Base) :
    posRoots P b ≃ {w : P.weylGroup // finrank K (M ⧸ (P.weylGroupRootRep w).fixedSubmodule) = 1} :=
  Equiv.ofBijective
    (fun i ↦ ⟨weylGroup.ofIdx P i.1, P.finrank_quotient_fixedSubmodule_weylGroupRootRep_ofIdx i.1⟩)
    ⟨fun i j h ↦ Subtype.ext (P.ofIdx_injOn_posRoots b i.2 j.2 (congrArg Subtype.val h)),
      fun w ↦ by
        obtain ⟨i, hi, hwi⟩ :=
          (P.finrank_quotient_fixedSubmodule_weylGroupRootRep_eq_one_iff_exists_mem_posRoots b).mp
            w.2
        exact ⟨⟨i, hi⟩, Subtype.ext hwi.symm⟩⟩

/-- Evaluating `posRootsEquivPseudoreflections` gives the corresponding root reflection. -/
@[simp]
theorem coe_posRootsEquivPseudoreflections_apply (b : P.Base) (i : posRoots P b) :
    (P.posRootsEquivPseudoreflections b i : P.weylGroup) = weylGroup.ofIdx P i := by
  rw [posRootsEquivPseudoreflections]
  rfl

/-- **The number of pseudoreflections of `P.weylGroupRootRep` equals the number of positive
roots.** -/
theorem natCard_pseudoreflections_weylGroupRootRep_eq_ncard_posRoots (b : P.Base) :
    Nat.card {w : P.weylGroup // finrank K (M ⧸ (P.weylGroupRootRep w).fixedSubmodule) = 1} =
      (posRoots P b).ncard := by
  rw [← Nat.card_coe_set_eq (posRoots P b)]
  exact (Nat.card_congr (P.posRootsEquivPseudoreflections b)).symm

/-- Twice the number of pseudoreflections of `P.weylGroupRootRep` is the total number of roots. -/
theorem two_mul_natCard_pseudoreflections_weylGroupRootRep_of_base (b : P.Base) :
    2 * Nat.card {w : P.weylGroup // finrank K (M ⧸ (P.weylGroupRootRep w).fixedSubmodule) = 1} =
      Nat.card ι := by
  rw [P.natCard_pseudoreflections_weylGroupRootRep_eq_ncard_posRoots b, two_mul_ncard_posRoots P b]

/-- A subspace of `M` is a reflecting hyperplane of `P.weylGroupRootRep` if and only if it is the
kernel of some coroot functional `P.coroot' i`. -/
theorem mem_reflectingHyperplanes_weylGroupRootRep_iff_of_base (b : P.Base) {H : Submodule K M} :
    letI := P.finite_weylGroup_of_base b
    H ∈ P.weylGroupRootRep.reflectingHyperplanes ↔ ∃ i : ι, LinearMap.ker (P.coroot' i) = H := by
  let := P.finite_weylGroup_of_base b
  rw [Representation.mem_reflectingHyperplanes]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨i, rfl⟩ :=
      (P.finrank_quotient_fixedSubmodule_weylGroupRootRep_eq_one_iff_of_base b).mp hw
    exact ⟨i, (P.fixedSubmodule_weylGroupRootRep_ofIdx i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨weylGroup.ofIdx P i, P.finrank_quotient_fixedSubmodule_weylGroupRootRep_ofIdx i,
      P.fixedSubmodule_weylGroupRootRep_ofIdx i⟩

/-- A subspace of `M` is a reflecting hyperplane of `P.weylGroupRootRep` if and only if it is the
kernel of `P.coroot' i` for a positive root `i ∈ posRoots P b`. -/
theorem mem_reflectingHyperplanes_weylGroupRootRep_iff_exists_mem_posRoots (b : P.Base)
    {H : Submodule K M} :
    letI := P.finite_weylGroup_of_base b
    H ∈ P.weylGroupRootRep.reflectingHyperplanes ↔
      ∃ i ∈ posRoots P b, LinearMap.ker (P.coroot' i) = H := by
  let := P.finite_weylGroup_of_base b
  rw [P.mem_reflectingHyperplanes_weylGroupRootRep_iff_of_base b]
  refine ⟨?_, fun ⟨i, _, hi⟩ ↦ ⟨i, hi⟩⟩
  rintro ⟨i, rfl⟩
  by_cases hi : b.IsPos i
  · exact ⟨i, (mem_posRoots P b i).mpr hi, rfl⟩
  · let := P.indexNeg
    refine ⟨-i, (mem_posRoots P b (-i)).mpr ((Base.IsPos.neg_iff_not b i).mpr hi), ?_⟩
    rw [indexNeg_neg, P.coroot'_reflectionPerm_self, LinearMap.ker_neg]

/-- Every coroot hyperplane belongs to the reflecting arrangement of `P.weylGroupRootRep`. -/
theorem ker_coroot'_mem_reflectingHyperplanes_weylGroupRootRep (b : P.Base) (i : ι) :
    letI := P.finite_weylGroup_of_base b
    LinearMap.ker (P.coroot' i) ∈ P.weylGroupRootRep.reflectingHyperplanes :=
  (P.mem_reflectingHyperplanes_weylGroupRootRep_iff_of_base b).mpr ⟨i, rfl⟩

/-- **Bijection between the positive roots of a base and the reflecting hyperplanes of
`P.weylGroupRootRep`.** -/
noncomputable def posRootsEquivReflectingHyperplanes (b : P.Base) :
    letI := P.finite_weylGroup_of_base b
    posRoots P b ≃ P.weylGroupRootRep.reflectingHyperplanes := by
  let := P.finite_weylGroup_of_base b
  exact Equiv.ofBijective
    (fun i ↦ ⟨LinearMap.ker (P.coroot' i.1),
      P.ker_coroot'_mem_reflectingHyperplanes_weylGroupRootRep b i.1⟩)
    ⟨fun i j h ↦ Subtype.ext (P.ker_coroot'_injOn_posRoots b i.2 j.2 (congrArg Subtype.val h)),
      fun H ↦ by
        obtain ⟨i, hi, hHi⟩ :=
          (P.mem_reflectingHyperplanes_weylGroupRootRep_iff_exists_mem_posRoots b).mp H.2
        exact ⟨⟨i, hi⟩, Subtype.ext hHi⟩⟩

/-- Evaluating `posRootsEquivReflectingHyperplanes` gives the coroot hyperplane
`LinearMap.ker (P.coroot' i)`. -/
@[simp]
theorem coe_posRootsEquivReflectingHyperplanes_apply (b : P.Base) (i : posRoots P b) :
    letI := P.finite_weylGroup_of_base b
    (P.posRootsEquivReflectingHyperplanes b i : Submodule K M) = LinearMap.ker (P.coroot' i) := by
  rw [posRootsEquivReflectingHyperplanes]
  rfl

/-- The number of reflecting hyperplanes of `P.weylGroupRootRep` equals the number of positive
roots. -/
theorem card_reflectingHyperplanes_weylGroupRootRep_eq_ncard_posRoots (b : P.Base) :
    letI := P.finite_weylGroup_of_base b
    P.weylGroupRootRep.reflectingHyperplanes.card = (posRoots P b).ncard := by
  let := P.finite_weylGroup_of_base b
  rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card, ← Nat.card_coe_set_eq (posRoots P b)]
  exact (Nat.card_congr (P.posRootsEquivReflectingHyperplanes b)).symm

/-- **Pointwise stabilizer of a coroot hyperplane.** An element of `P.weylGroup` fixes
`LinearMap.ker (P.coroot' i)` pointwise if and only if it is `1` or `weylGroup.ofIdx P i`. -/
theorem ker_coroot'_le_fixedSubmodule_weylGroupRootRep_iff (b : P.Base) (i : ι) (w : P.weylGroup) :
    LinearMap.ker (P.coroot' i) ≤ (P.weylGroupRootRep w).fixedSubmodule ↔
      w = 1 ∨ w = weylGroup.ofIdx P i := by
  let := P.finite_weylGroup_of_base b
  -- Replace `i` by a positive root index with the same kernel and reflection.
  suffices hpos : ∀ j ∈ posRoots P b,
      LinearMap.ker (P.coroot' j) ≤ (P.weylGroupRootRep w).fixedSubmodule ↔
        w = 1 ∨ w = weylGroup.ofIdx P j by
    by_cases hi : b.IsPos i
    · exact hpos i ((mem_posRoots P b i).mpr hi)
    · let := P.indexNeg
      have hneg : -i ∈ posRoots P b :=
        (mem_posRoots P b (-i)).mpr ((Base.IsPos.neg_iff_not b i).mpr hi)
      have hker : LinearMap.ker (P.coroot' (-i)) = LinearMap.ker (P.coroot' i) := by
        rw [indexNeg_neg, P.coroot'_reflectionPerm_self, LinearMap.ker_neg]
      simpa only [hker, weylGroup.ofIdx_neg] using hpos (-i) hneg
  intro j hj
  have hmem := P.ker_coroot'_mem_reflectingHyperplanes_weylGroupRootRep b j
  rw [P.weylGroupRootRep.le_fixedSubmodule_iff_of_mem_reflectingHyperplanes hmem w,
    ← map_one P.weylGroupRootRep, P.weylGroupRootRep_injective.eq_iff]
  refine or_congr_right ⟨fun hfix ↦ ?_, fun hw ↦ hw ▸ P.fixedSubmodule_weylGroupRootRep_ofIdx j⟩
  have hfin : finrank K (M ⧸ (P.weylGroupRootRep w).fixedSubmodule) = 1 := by
    rw [hfix]
    exact (P.coroot' j).finrank_quotient_ker_eq_one_of_ne_zero (P.coroot'_ne_zero j)
  obtain ⟨k, hk, rfl⟩ :=
    (P.finrank_quotient_fixedSubmodule_weylGroupRootRep_eq_one_iff_exists_mem_posRoots b).mp hfin
  rw [P.fixedSubmodule_weylGroupRootRep_ofIdx] at hfix
  rw [P.ker_coroot'_injOn_posRoots b hk hj hfix]

/-- **Regular weights are the complement of the reflecting-hyperplane arrangement.** Relative to a
base `b`, a weight is regular (`P.IsRegularWeight`) if and only if it lies in no reflecting
hyperplane of `P.weylGroupRootRep`. -/
theorem isRegularWeight_iff_forall_notMem_reflectingHyperplanes_of_base (b : P.Base) (x : M) :
    letI := P.finite_weylGroup_of_base b
    P.IsRegularWeight x ↔ ∀ H ∈ P.weylGroupRootRep.reflectingHyperplanes, x ∉ H := by
  let := P.finite_weylGroup_of_base b
  rw [isRegularWeight_iff]
  constructor
  · intro hreg H hH hx
    obtain ⟨i, rfl⟩ := (P.mem_reflectingHyperplanes_weylGroupRootRep_iff_of_base b).mp hH
    exact hreg i (LinearMap.mem_ker.mp hx)
  · intro h i hi
    exact h (LinearMap.ker (P.coroot' i))
      (P.ker_coroot'_mem_reflectingHyperplanes_weylGroupRootRep b i) (LinearMap.mem_ker.mpr hi)

section IsRootSystem

variable [P.IsRootSystem]

/-- On a finite reduced crystallographic root system in characteristic zero, the pseudoreflections
of `P.weylGroupRootRep` are precisely the root reflections `weylGroup.ofIdx P i`. -/
theorem finrank_quotient_fixedSubmodule_weylGroupRootRep_eq_one_iff {w : P.weylGroup} :
    finrank K (M ⧸ (P.weylGroupRootRep w).fixedSubmodule) = 1 ↔
      ∃ i : ι, w = weylGroup.ofIdx P i := by
  obtain ⟨b⟩ := P.nonempty_base
  exact P.finrank_quotient_fixedSubmodule_weylGroupRootRep_eq_one_iff_of_base b

/-- Twice the number of pseudoreflections of a finite reduced crystallographic root system in
characteristic zero is the number of roots. -/
theorem two_mul_natCard_pseudoreflections_weylGroupRootRep :
    2 * Nat.card {w : P.weylGroup // finrank K (M ⧸ (P.weylGroupRootRep w).fixedSubmodule) = 1} =
      Nat.card ι := by
  obtain ⟨b⟩ := P.nonempty_base
  exact P.two_mul_natCard_pseudoreflections_weylGroupRootRep_of_base b

/-- On a finite reduced crystallographic root system in characteristic zero, the reflecting
hyperplanes of `P.weylGroupRootRep` are precisely the coroot hyperplanes `ker (P.coroot' i)`. -/
theorem mem_reflectingHyperplanes_weylGroupRootRep_iff {H : Submodule K M} :
    letI := P.finite_weylGroup
    H ∈ P.weylGroupRootRep.reflectingHyperplanes ↔ ∃ i : ι, LinearMap.ker (P.coroot' i) = H := by
  obtain ⟨b⟩ := P.nonempty_base
  exact P.mem_reflectingHyperplanes_weylGroupRootRep_iff_of_base b

/-- On a finite reduced crystallographic root system in characteristic zero, a weight is regular if
and only if it lies in no reflecting hyperplane of `P.weylGroupRootRep`. -/
theorem isRegularWeight_iff_forall_notMem_reflectingHyperplanes (x : M) :
    letI := P.finite_weylGroup
    P.IsRegularWeight x ↔ ∀ H ∈ P.weylGroupRootRep.reflectingHyperplanes, x ∉ H := by
  obtain ⟨b⟩ := P.nonempty_base
  exact P.isRegularWeight_iff_forall_notMem_reflectingHyperplanes_of_base b x

/-- On a finite reduced crystallographic root system in characteristic zero, the characteristic
polynomial of any Weyl-group element on `M` is the scalar extension of an integer polynomial. -/
theorem exists_map_int_eq_charpoly_weylGroupRootRep [Module.Finite K M] (w : P.weylGroup) :
    ∃ p : Polynomial ℤ, p.map (algebraMap ℤ K) = (P.weylGroupRootRep w).charpoly := by
  obtain ⟨b⟩ := P.nonempty_base
  exact P.exists_map_int_eq_charpoly_weylGroupRootRep_of_base b w

/-- On a finite reduced crystallographic root system in characteristic zero, the characteristic
polynomial of any Weyl-group element on `M` is the scalar extension of a rational polynomial. -/
theorem exists_map_rat_eq_charpoly_weylGroupRootRep [Module.Finite K M] (w : P.weylGroup) :
    ∃ p : Polynomial ℚ, p.map (algebraMap ℚ K) = (P.weylGroupRootRep w).charpoly := by
  obtain ⟨b⟩ := P.nonempty_base
  exact P.exists_map_rat_eq_charpoly_weylGroupRootRep_of_base b w

end IsRootSystem

end Classification

end Field

end RootPairing
