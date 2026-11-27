/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.Weyl.Coxeter
public import TauCeti.LinearAlgebra.RootSystem.Affine.Realization
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Affine.Alcove
import TauCeti.GroupTheory.Coxeter.Matsumoto
import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.Weyl.TitsCone

/-!
# The affine Weyl group is a Coxeter group

Let `b` be a base of a finite, reduced, irreducible, crystallographic root pairing `P` over a
linearly ordered field `R`, with simple roots `αᵢ` and highest root `θ`. This file
proves that the affine Weyl group `W_aff` (`RootPairing.affineWeylGroup`) is a Coxeter system for
the Coxeter matrix `TauCeti.coxeterMatrixOfGeneralizedCartanMatrix` of the affine Cartan matrix
`A = RootPairing.Base.affineCartanMatrix`, whose simple reflections are the reflections in the
walls of the fundamental alcove `RootPairing.fundamentalAlcove`
(`RootPairing.Base.affineSimpleReflection`): `s_{θ,1}` at the affine node `none` and `s_{αᵢ,0}` at
the node of `αᵢ`, the nodes `Option b.support` that index the affine
simple roots `RootPairing.Base.affineSimpleRoot`.

The exchange property is not proved again. Instead `W_aff` is identified with the Weyl group of a
realization of `A`, which is a Coxeter group by Kac's Proposition 3.13
(`TauCeti.CartanRealization.weylCoxeterSystem`), and the Coxeter system is transported along the
identification. The realization `RootPairing.Base.affineRealization` lives on `H = M × R × R`.
In its dual the point `x` of the coweight space `N` sits at level one as the functional
`λₓ(m, s, t) = ⟨m, x⟩ + s`, whose value at the coroot of the node `k` is the affine simple root
`aₖ(x)`. A simple reflection of the realization carries `λₓ` to `λ_y`, with `y` the image of `x`
under the wall reflection, plus a multiple of the functional `τ(m, s, t) = t`, which the whole Weyl
group fixes. Consequently:

* the wall reflections satisfy the Coxeter relations, because the simple reflections of the
  realization do, so the Coxeter presentation of the Weyl group of the realization gives a
  homomorphism to `W_aff` sending each simple reflection to a wall reflection;
* it is injective: an element mapped to `1` moves `λₓ`, for `x` in the fundamental alcove, by a
  multiple of `τ` and hence to a dominant weight, so it fixes `λₓ` by the fundamental domain
  property of the dominant chamber (`TauCeti.CartanRealization.isDominant_smul_iff_eq`), and the
  stabilizer of the strictly dominant weight `λₓ` is trivial
  (`TauCeti.CartanRealization.parabolic_eq_stabilizer`);
* it is surjective: the wall reflections carry into the closed fundamental alcove every point at
  which every root is bounded below by an integer
  (`RootPairing.exists_mem_apply_mem_closedFundamentalAlcove_of_affineCoreflection_mem`), as is the
  image `f x` of a point `x` of the fundamental alcove under any `f ∈ W_aff`
  (`RootPairing.exists_intCast_lt_root'_apply_of_mem_affineWeylGroup`); and the affine Weyl group
  acts freely on the translates of the fundamental alcove
  (`RootPairing.eq_one_of_mem_affineWeylGroup_of_apply_mem_fundamentalAlcove`), so every element
  of `W_aff` is a product of wall reflections.

The Weyl groups of any two realizations of `A` over fields of characteristic zero are identified
(`TauCeti.CartanRealization.weylGroupEquiv`), so `W_aff` is the Weyl group of every such
realization.

For `x` in the fundamental alcove, the length of `f ∈ W_aff` is the number of affine roots
`αⱼ - k` positive at `x` and negative at `f x` (`RootPairing.separatingAffineRoots`), that is the
number of affine root hyperplanes separating the fundamental alcove from its image under `f`.
A wall reflection changes this number by exactly one
(`RootPairing.ncard_separatingAffineRoots_affineSimpleReflection_add_one_of_affineSimpleRoot_neg`),
so it is at most the length; descending through the walls separating `f x` from the alcove shows
that it is at least the length.

## Main definitions

* `RootPairing.Base.affineWeylGroupEquiv`: the isomorphism of the affine Weyl group with the Weyl
  group of any realization of the affine Cartan matrix over a field of characteristic zero,
  carrying the wall reflections to the simple reflections.
* `RootPairing.Base.affineWeylCoxeterSystem`: the Coxeter system of the affine Weyl group.

## Main results

* `RootPairing.Base.affineWeylGroupEquiv_affineCoreflection_highestRoot` and
  `RootPairing.Base.affineWeylGroupEquiv_toAffineEquiv_coreflection`: the isomorphism carries
  `s_{θ,1}` and `s_{αᵢ,0} = s_{αᵢ}` to the simple reflections at the affine node and at the node
  of `αᵢ`.
* `RootPairing.Base.coe_affineWeylCoxeterSystem_simple`,
  `RootPairing.Base.coe_affineWeylCoxeterSystem_simple_none` and
  `RootPairing.Base.coe_affineWeylCoxeterSystem_simple_some`: the simple reflections of the
  Coxeter system are the wall reflections.
* `RootPairing.Base.affineWeylCoxeterSystem_length`: **the length of an element is the number of
  affine root hyperplanes separating the fundamental alcove from its image.**

The file ends with the checks in type `A₁`, where the highest root is simple: the two nodes have
Coxeter matrix entry `0`, so the group is the infinite dihedral group, the product of the two
simple reflections is the translation by the coroot and has infinite order, and that translation
has length `2`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Ch. V, §3 and Ch. VI, §2.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge Studies in Advanced
  Mathematics 29, §4.3–§4.6.
* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, Proposition 3.13 and §6.5–§6.6.
-/

public section

open Module TauCeti
open TauCeti.CartanRealization (diag_map_intCast)

namespace RootPairing.Base

variable {ι R M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-! ### The affine Weyl group as the Weyl group of the affine realization -/

section Comparison

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Module R M] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [Nonempty ι] (b : P.Base)

variable [P.IsCrystallographic]

local notation "W" =>
  b.affineRealization.weylGroup (diag_map_intCast b.affineCartanMatrix_apply_same)

variable (P) in
/-- The point `x` of the coweight space at level one in the dual of the affine realization: the
functional `(m, s, t) ↦ ⟨m, x⟩ + s`, whose value at the coroot at `k` is `aₖ(x)`. -/
private noncomputable def levelPoint (x : N) : Dual R (M × R × R) :=
  (P.toLinearMap.flip x).coprod (LinearMap.fst R R R)

variable (R M) in
/-- The functional `(m, s, t) ↦ t`, which vanishes on every coroot of the affine realization and
is therefore fixed by its Weyl group. -/
private def levelShift : Dual R (M × R × R) :=
  (0 : Dual R M).coprod (LinearMap.snd R R R)

private lemma levelPoint_coroot (x : N) (k : Option b.support) :
    levelPoint P x (b.affineRealization.coroot k) = b.affineSimpleRoot k x := by
  rw [b.affineSimpleRoot_eq_root'_add k x]
  simp [levelPoint]

private lemma levelShift_coroot (k : Option b.support) :
    levelShift R M (b.affineRealization.coroot k) = 0 := by
  simp [levelShift]

private lemma smul_levelShift (w : W) : w • levelShift R M = levelShift R M := by
  refine b.affineRealization.weylGroup_induction _
    (P := fun w ↦ w • levelShift R M = levelShift R M) (one_smul _ _) (fun k ↦ ?_)
    (fun u v hu hv ↦ by rw [mul_smul, hv, hu]) w
  rw [Subgroup.smul_def, LinearEquiv.smul_def, CartanRealization.coe_weylSimple,
    CartanRealization.simpleReflection_apply, levelShift_coroot, zero_smul, sub_zero]

/-- A simple reflection of the affine realization moves a point at level one as the wall
reflection moves the point, up to a multiple of `levelShift`. -/
private lemma weylSimple_smul_levelPoint (k : Option b.support) (x : N) :
    b.affineRealization.weylSimple (diag_map_intCast b.affineCartanMatrix_apply_same) k •
      levelPoint P x =
      levelPoint P (b.affineSimpleReflection k x) +
        (-(b.affineSimpleRoot k x * b.affineSimpleRoot k 0)) • levelShift R M := by
  refine LinearMap.ext fun ⟨m, s, t⟩ ↦ ?_
  simp only [Subgroup.smul_def, LinearEquiv.smul_def, CartanRealization.coe_weylSimple,
    CartanRealization.simpleReflection_apply, levelPoint_coroot, affineSimpleReflection_apply]
  simp only [levelPoint, levelShift, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.coprod_apply, affineRealization_root_apply, map_sub,
    map_smul, LinearMap.flip_apply, LinearMap.fst_apply, LinearMap.snd_apply,
    LinearMap.zero_apply, smul_eq_mul, LinearMap.sub_apply]
  ring

/-- An element `w` of the Weyl group of the affine realization **intertwines** an affine map `f`
of the coweight space when it moves every point at level one as `f` moves the point, up to a
multiple of `levelShift`. -/
private def Intertwines (w : W) (f : N ≃ᵃ[R] N) : Prop :=
  ∀ x, ∃ c : R, w • levelPoint P x = levelPoint P (f x) + c • levelShift R M

private lemma intertwines_weylSimple (k : Option b.support) :
    Intertwines b
      (b.affineRealization.weylSimple (diag_map_intCast b.affineCartanMatrix_apply_same) k)
      (b.affineSimpleReflection k) :=
  fun x ↦ ⟨_, b.weylSimple_smul_levelPoint k x⟩

private lemma Intertwines.mul {w w' : W} {f f' : N ≃ᵃ[R] N} (h : Intertwines b w f)
    (h' : Intertwines b w' f') : Intertwines b (w * w') (f * f') := by
  intro x
  obtain ⟨c', hc'⟩ := h' x
  obtain ⟨c, hc⟩ := h (f' x)
  refine ⟨c + c', ?_⟩
  rw [AffineEquiv.coe_mul, Function.comp_apply, mul_smul, hc', smul_add, hc, smul_comm,
    b.smul_levelShift, add_smul, add_assoc]

private lemma Intertwines.pow {w : W} {f : N ≃ᵃ[R] N} (h : Intertwines b w f) (n : ℕ) :
    Intertwines b (w ^ n) (f ^ n) := by
  induction n with
  | zero => exact fun x ↦ ⟨0, by simp⟩
  | succ n ih => simpa only [pow_succ] using ih.mul b h

/-- An affine map intertwined by the identity is the identity. -/
private lemma eq_one_of_intertwines_one {f : N ≃ᵃ[R] N} (h : Intertwines b 1 f) : f = 1 := by
  ext x
  obtain ⟨c, hc⟩ := h x
  have : P.toLinearMap.flip (f x) = P.toLinearMap.flip x := LinearMap.ext fun m ↦ by
    simpa [levelPoint, levelShift] using congr(($hc) (m, 0, 0)).symm
  exact (LinearMap.IsPerfPair.bijective_right P.toLinearMap).injective this

section DecidableComparison

variable [DecidableEq ι]

/-- The Coxeter system of the Weyl group of the affine realization. -/
private noncomputable abbrev realizationCoxeterSystem :
    CoxeterSystem (coxeterMatrixOfGeneralizedCartanMatrix b.affineCartanMatrix) W :=
  b.affineRealization.weylCoxeterSystem b.affineCartanMatrix_apply_same
    (fun _ _ ↦ b.affineCartanMatrix_le_zero_of_ne)
    (fun _ _ ↦ b.affineCartanMatrix_apply_eq_zero_iff_symm)

/-- The wall reflections satisfy the Coxeter relations of the affine Cartan matrix, since the simple
reflections of the affine realization do. -/
private lemma isLiftable_affineSimpleReflection :
    (coxeterMatrixOfGeneralizedCartanMatrix b.affineCartanMatrix).IsLiftable
      fun k ↦ (⟨b.affineSimpleReflection k, b.affineSimpleReflection_mem_affineWeylGroup k⟩ :
        P.affineWeylGroup) := by
  intro k l
  have hrel := b.realizationCoxeterSystem.simple_mul_simple_pow k l
  simp only [CartanRealization.weylCoxeterSystem_simple] at hrel
  have h := ((b.intertwines_weylSimple k).mul b (b.intertwines_weylSimple l)).pow b
    (coxeterMatrixOfGeneralizedCartanMatrix b.affineCartanMatrix k l)
  rw [hrel] at h
  exact Subtype.ext (b.eq_one_of_intertwines_one h)

/-- The homomorphism from the Weyl group of the affine realization to the affine Weyl group sending
each simple reflection to the reflection in the corresponding wall of the fundamental alcove. -/
private noncomputable def toAffineWeylGroup : W →* P.affineWeylGroup :=
  b.realizationCoxeterSystem.lift ⟨_, b.isLiftable_affineSimpleReflection⟩

private lemma toAffineWeylGroup_weylSimple (k : Option b.support) :
    b.toAffineWeylGroup
        (b.affineRealization.weylSimple (diag_map_intCast b.affineCartanMatrix_apply_same) k) =
      ⟨b.affineSimpleReflection k, b.affineSimpleReflection_mem_affineWeylGroup k⟩ := by
  rw [← CartanRealization.weylCoxeterSystem_simple b.affineRealization
    b.affineCartanMatrix_apply_same (fun _ _ ↦ b.affineCartanMatrix_le_zero_of_ne)
    (fun _ _ ↦ b.affineCartanMatrix_apply_eq_zero_iff_symm)]
  exact b.realizationCoxeterSystem.lift_apply_simple b.isLiftable_affineSimpleReflection k

private lemma intertwines_toAffineWeylGroup (w : W) :
    Intertwines b w (b.toAffineWeylGroup w) := by
  refine b.realizationCoxeterSystem.simple_induction
    (p := fun w ↦ Intertwines b w (b.toAffineWeylGroup w)) w (fun k ↦ ?_)
    (fun x ↦ ⟨0, by simp⟩) fun w w' hw hw' ↦ ?_
  · simp only [CartanRealization.weylCoxeterSystem_simple, toAffineWeylGroup_weylSimple]
    exact b.intertwines_weylSimple k
  · rw [map_mul, Subgroup.coe_mul]
    exact hw.mul b hw'

/-- The comparison is injective: an element of the Weyl group of the affine realization acting
trivially on the alcoves fixes a strictly dominant point at level one, by the fundamental domain
property of the dominant chamber, so it is trivial. -/
private lemma toAffineWeylGroup_injective : Function.Injective b.toAffineWeylGroup := by
  refine (injective_iff_map_eq_one _).mpr fun w hw ↦ ?_
  have h := b.intertwines_toAffineWeylGroup w
  rw [hw, OneMemClass.coe_one] at h
  obtain ⟨x, hx⟩ := fundamentalAlcove_nonempty b
  have hpos := (mem_fundamentalAlcove_iff_forall_affineSimpleRoot_pos b).mp hx
  have hdom : b.affineRealization.IsDominant (levelPoint P x) :=
    CartanRealization.isDominant_iff.mpr fun k ↦ by
    rw [b.levelPoint_coroot]
    exact (hpos k).le
  obtain ⟨c, hc⟩ := h x
  have hdom' : b.affineRealization.IsDominant (w • levelPoint P x) :=
    CartanRealization.isDominant_iff.mpr fun k ↦ by
    rw [hc, LinearMap.add_apply, LinearMap.smul_apply, b.levelShift_coroot, smul_zero, add_zero,
      AffineEquiv.coe_one, id_eq, b.levelPoint_coroot]
    exact (hpos k).le
  have hfix := (b.affineRealization.isDominant_smul_iff_eq b.affineCartanMatrix_apply_same
    (fun _ _ ↦ b.affineCartanMatrix_le_zero_of_ne)
    (fun _ _ ↦ b.affineCartanMatrix_apply_eq_zero_iff_symm) w hdom).mp hdom'
  have hstab : w ∈ MulAction.stabilizer W (levelPoint P x) := MulAction.mem_stabilizer_iff.mpr hfix
  rw [← b.affineRealization.parabolic_eq_stabilizer b.affineCartanMatrix_apply_same
    (fun _ _ ↦ b.affineCartanMatrix_le_zero_of_ne)
    (fun _ _ ↦ b.affineCartanMatrix_apply_eq_zero_iff_symm) hdom] at hstab
  have hempty : {k | levelPoint P x (b.affineRealization.coroot k) = 0} = ∅ :=
    Set.eq_empty_of_forall_notMem fun k hk ↦ by
      rw [Set.mem_ofPred_eq, b.levelPoint_coroot] at hk
      exact (hpos k).ne' hk
  rwa [hempty, CoxeterSystem.parabolic_empty, Subgroup.mem_bot] at hstab

variable [P.IsReduced] [P.IsIrreducible]

/-- The comparison is surjective: the wall reflections generate the affine Weyl group, since they
carry the image of the fundamental alcove under any element of the affine Weyl group back to the
fundamental alcove, and the affine Weyl group acts freely on these translates of the alcove. -/
private lemma toAffineWeylGroup_surjective : Function.Surjective b.toAffineWeylGroup := by
  rintro ⟨f, hf⟩
  set G : Subgroup (N ≃ᵃ[R] N) := b.toAffineWeylGroup.range.map P.affineWeylGroup.subtype
  have hwall (k : Option b.support) : b.affineSimpleReflection k ∈ G :=
    ⟨_, ⟨_, b.toAffineWeylGroup_weylSimple k⟩, rfl⟩
  obtain ⟨x, hx⟩ := fundamentalAlcove_nonempty b
  obtain ⟨ω, hω, -⟩ := exists_wallWord_eq_inv_of_mem_affineWeylGroup b hf hx
  have hg := b.list_prod_map_affineSimpleReflection_mem hwall ω
  have hfG : f ∈ G := by
    rw [hω] at hg
    exact inv_mem_iff.mp hg
  obtain ⟨f', ⟨w, hw⟩, hf'⟩ := hfG
  exact ⟨w, hw.trans (Subtype.ext hf')⟩

private lemma toAffineWeylGroup_bijective : Function.Bijective b.toAffineWeylGroup :=
  ⟨b.toAffineWeylGroup_injective, b.toAffineWeylGroup_surjective⟩

end DecidableComparison

variable [P.IsReduced] [P.IsIrreducible]

/-- **The affine Weyl group is the Weyl group of the affine Cartan matrix.** For every realization
`R'` of the affine Cartan matrix over a field of characteristic zero, for instance
`RootPairing.Base.affineRealization`, the affine Weyl group is isomorphic to the Weyl group of
`R'`, by an isomorphism carrying the reflection in each wall of the fundamental alcove, `s_{θ,1}`
and the `s_{αᵢ,0}`, to the simple reflection at the corresponding node of the affine Dynkin diagram
(`RootPairing.Base.affineWeylGroupEquiv_affineCoreflection_highestRoot` and
`RootPairing.Base.affineWeylGroupEquiv_toAffineEquiv_coreflection`). -/
noncomputable def affineWeylGroupEquiv {K H : Type*} [Field K] [CharZero K] [AddCommGroup H]
    [Module K H] (R' : CartanRealization (b.affineCartanMatrix.map (Int.cast : ℤ → K)) H) :
    P.affineWeylGroup ≃* R'.weylGroup (diag_map_intCast b.affineCartanMatrix_apply_same) := by
  classical
  exact (MulEquiv.ofBijective b.toAffineWeylGroup b.toAffineWeylGroup_bijective).symm.trans
    (b.affineRealization.weylGroupEquiv R' b.affineCartanMatrix_apply_same
      (fun _ _ ↦ b.affineCartanMatrix_le_zero_of_ne)
      (fun _ _ ↦ b.affineCartanMatrix_apply_eq_zero_iff_symm))

private lemma affineWeylGroupEquiv_affineSimpleReflection {K H : Type*} [Field K] [CharZero K]
    [AddCommGroup H] [Module K H]
    (R' : CartanRealization (b.affineCartanMatrix.map (Int.cast : ℤ → K)) H)
    (k : Option b.support) :
    b.affineWeylGroupEquiv R'
        ⟨b.affineSimpleReflection k, b.affineSimpleReflection_mem_affineWeylGroup k⟩ =
      R'.weylSimple (diag_map_intCast b.affineCartanMatrix_apply_same) k := by
  classical
  rw [affineWeylGroupEquiv, MulEquiv.trans_apply, ← b.toAffineWeylGroup_weylSimple,
    ← MulEquiv.ofBijective_apply _ b.toAffineWeylGroup_bijective, MulEquiv.symm_apply_apply,
    CartanRealization.weylGroupEquiv_weylSimple]

/-- The isomorphism `RootPairing.Base.affineWeylGroupEquiv` carries the reflection in the wall
`θ = 1` to the simple reflection at the affine node. -/
@[simp]
lemma affineWeylGroupEquiv_affineCoreflection_highestRoot {K H : Type*} [Field K] [CharZero K]
    [AddCommGroup H] [Module K H]
    (R' : CartanRealization (b.affineCartanMatrix.map (Int.cast : ℤ → K)) H)
    (h : P.affineCoreflection b.highestRoot 1 ∈ P.affineWeylGroup) :
    b.affineWeylGroupEquiv R' ⟨_, h⟩ =
      R'.weylSimple (diag_map_intCast b.affineCartanMatrix_apply_same) none := by
  simpa only [affineSimpleReflection_none] using
    b.affineWeylGroupEquiv_affineSimpleReflection R' none

/-- The isomorphism `RootPairing.Base.affineWeylGroupEquiv` carries the reflection in the wall
`αᵢ = 0`, the coreflection `s_{αᵢ}` (`RootPairing.affineCoreflection_zero`), to the simple
reflection at the node of `αᵢ`. -/
@[simp]
lemma affineWeylGroupEquiv_toAffineEquiv_coreflection {K H : Type*} [Field K] [CharZero K]
    [AddCommGroup H] [Module K H]
    (R' : CartanRealization (b.affineCartanMatrix.map (Int.cast : ℤ → K)) H) (i : b.support)
    (h : (P.coreflection i).toAffineEquiv ∈ P.affineWeylGroup) :
    b.affineWeylGroupEquiv R' ⟨_, h⟩ =
      R'.weylSimple (diag_map_intCast b.affineCartanMatrix_apply_same) (some i) := by
  simpa only [affineSimpleReflection_some] using
    b.affineWeylGroupEquiv_affineSimpleReflection R' (some i)

variable [DecidableEq ι]

/-- **The affine Weyl group is a Coxeter group.** For a finite, reduced, irreducible,
crystallographic root pairing over a linearly ordered field, the affine Weyl group is
a Coxeter system for the Coxeter matrix of the affine Cartan matrix, whose simple reflections are
the reflections in the walls of the fundamental alcove: `s_{θ,1}` at the affine node `none` and
`s_{αᵢ,0}` at the node of a simple root `αᵢ`. It is transported from the Coxeter system
`TauCeti.CartanRealization.weylCoxeterSystem` of the Weyl group of the affine realization along
the isomorphism `RootPairing.Base.affineWeylGroupEquiv`. -/
noncomputable def affineWeylCoxeterSystem :
    CoxeterSystem (coxeterMatrixOfGeneralizedCartanMatrix b.affineCartanMatrix) P.affineWeylGroup :=
  b.realizationCoxeterSystem.map (b.affineWeylGroupEquiv b.affineRealization).symm

/-- The simple reflection of `RootPairing.Base.affineWeylCoxeterSystem` at a node `k` of the affine
Dynkin diagram is the reflection in the wall of the fundamental alcove at `k`. -/
lemma coe_affineWeylCoxeterSystem_simple (k : Option b.support) :
    (b.affineWeylCoxeterSystem.simple k : N ≃ᵃ[R] N) = b.affineSimpleReflection k := by
  rw [affineWeylCoxeterSystem, CoxeterSystem.map_simple,
    CartanRealization.weylCoxeterSystem_simple, ← b.affineWeylGroupEquiv_affineSimpleReflection _ k,
    MulEquiv.symm_apply_apply]

/-- The simple reflection of `RootPairing.Base.affineWeylCoxeterSystem` at the affine node is the
reflection in the wall `θ = 1`. -/
@[simp]
lemma coe_affineWeylCoxeterSystem_simple_none :
    (b.affineWeylCoxeterSystem.simple none : N ≃ᵃ[R] N) = P.affineCoreflection b.highestRoot 1 :=
  (b.coe_affineWeylCoxeterSystem_simple none).trans b.affineSimpleReflection_none

/-- The simple reflection of `RootPairing.Base.affineWeylCoxeterSystem` at the node of a simple
root `αᵢ` is the reflection in the wall `αᵢ = 0`, the coreflection `s_{αᵢ}`
(`RootPairing.affineCoreflection_zero`). -/
@[simp]
lemma coe_affineWeylCoxeterSystem_simple_some (i : b.support) :
    (b.affineWeylCoxeterSystem.simple (some i) : N ≃ᵃ[R] N) = (P.coreflection i).toAffineEquiv := by
  rw [coe_affineWeylCoxeterSystem_simple, affineSimpleReflection_some]

/-! ### The length -/

/-- Multiplying by a simple reflection on the left changes the number of separating affine roots by
at most one. -/
private lemma ncard_separatingAffineRoots_simple_mul_le {x : N} (hx : x ∈ fundamentalAlcove P b)
    (f : P.affineWeylGroup) (k : Option b.support) :
    (P.separatingAffineRoots x
        (((b.affineWeylCoxeterSystem.simple k * f : P.affineWeylGroup) : N ≃ᵃ[R] N) x)).ncard ≤
      (P.separatingAffineRoots x ((f : N ≃ᵃ[R] N) x)).ncard + 1 := by
  rw [Subgroup.coe_mul, AffineEquiv.coe_mul, Function.comp_apply,
    b.coe_affineWeylCoxeterSystem_simple]
  have hy := P.root'_apply_ne_intCast_of_mem_affineWeylGroup f.property
    (root'_ne_intCast_of_mem_fundamentalAlcove hx)
  have hk : b.affineSimpleRoot k ((f : N ≃ᵃ[R] N) x) ≠ 0 := by
    rcases k with _ | i
    · rw [affineSimpleRoot_none, sub_ne_zero]
      exact fun h ↦ hy b.highestRoot 1 (by simpa using h.symm)
    · simpa using hy i 0
  have hbdd := P.exists_intCast_lt_root'_apply_of_mem_affineWeylGroup f.property
    (exists_intCast_lt_root'_of_mem_fundamentalAlcove hx)
  rcases hk.lt_or_gt with hk | hk
  · have := ncard_separatingAffineRoots_affineSimpleReflection_add_one_of_affineSimpleRoot_neg b hx
      hbdd hk
    omega
  · have := ncard_separatingAffineRoots_affineSimpleReflection_add_one_of_affineSimpleRoot_neg b hx
      (P.exists_intCast_lt_root'_apply_of_mem_affineWeylGroup
        (b.affineSimpleReflection_mem_affineWeylGroup k) hbdd)
      (by rw [affineSimpleRoot_affineSimpleReflection]; linarith)
    rw [affineSimpleReflection_affineSimpleReflection] at this
    omega

/-- **The length in the affine Weyl group counts the separating hyperplanes.** For a point `x` of
the fundamental alcove, the length of an element `f` of the affine Weyl group in the Coxeter system
`RootPairing.Base.affineWeylCoxeterSystem` is the number of affine roots `αⱼ - k` positive at `x`
and negative at `f x` (`RootPairing.separatingAffineRoots`): the number of affine root hyperplanes
separating the fundamental alcove from its image under `f`. -/
theorem affineWeylCoxeterSystem_length {x : N} (hx : x ∈ fundamentalAlcove P b)
    (f : P.affineWeylGroup) :
    b.affineWeylCoxeterSystem.length f = (P.separatingAffineRoots x ((f : N ≃ᵃ[R] N) x)).ncard := by
  set cs := b.affineWeylCoxeterSystem
  refine le_antisymm ?_ ?_
  · -- Use the same wall word as the subgroup-generation descent.
    have hprod (ω : List (Option b.support)) :
        (cs.wordProd ω : N ≃ᵃ[R] N) = (ω.map b.affineSimpleReflection).prod := by
      induction ω with
      | nil => simp
      | cons k ω ih =>
        dsimp only [cs] at ih ⊢
        simp only [CoxeterSystem.wordProd_cons, Subgroup.coe_mul,
          coe_affineWeylCoxeterSystem_simple, List.map_cons, List.prod_cons, ih]
    obtain ⟨ω, hω, hcount⟩ := exists_wallWord_eq_inv_of_mem_affineWeylGroup b f.property hx
    have hinv : cs.wordProd ω = f⁻¹ := Subtype.ext ((hprod ω).trans hω)
    have hlen : cs.length f ≤ ω.length := by
      rw [← cs.length_inv f, ← hinv]
      exact cs.length_wordProd_le ω
    omega
  · -- Each simple reflection in a reduced word adds at most one separating affine root.
    have key (ω : List (Option b.support)) :
        (P.separatingAffineRoots x (((cs.wordProd ω : P.affineWeylGroup) : N ≃ᵃ[R] N) x)).ncard ≤
          ω.length := by
      induction ω with
      | nil => simp
      | cons k ω ih =>
        rw [cs.wordProd_cons, List.length_cons]
        exact (b.ncard_separatingAffineRoots_simple_mul_le hx _ k).trans (by omega)
    obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced f
    rw [hω.eq]
    exact key ω

/-! ### Type `A₁` -/

section TypeA₁

variable {b} (hθ : b.highestRoot ∈ b.support)

omit [P.IsReduced] [P.IsIrreducible] in
include hθ in
/-- In type `A₁`, where the highest root is the simple root, the Coxeter matrix of the affine
Cartan matrix has the entry `0`, that is `∞`, at its two nodes: the affine Weyl group is the
infinite dihedral group. -/
private lemma affineCoxeterMatrix_none_highestRoot :
    coxeterMatrixOfGeneralizedCartanMatrix b.affineCartanMatrix none (some ⟨_, hθ⟩) = 0 := by
  rw [coxeterMatrixOfGeneralizedCartanMatrix_apply_of_ne _ (Option.some_ne_none _).symm]
  simp

include hθ in
/-- In type `A₁` the translation by the coroot is the product of the two simple reflections. -/
private lemma constVAdd_coroot_eq_simple_mul_simple :
    (b.affineWeylCoxeterSystem.simple none * b.affineWeylCoxeterSystem.simple (some ⟨_, hθ⟩) :
      P.affineWeylGroup) = ⟨AffineEquiv.constVAdd R N (P.coroot b.highestRoot),
        P.constVAdd_coroot_mem_affineWeylGroup _⟩ := by
  ext1
  rw [Subgroup.coe_mul, coe_affineWeylCoxeterSystem_simple_none,
    coe_affineWeylCoxeterSystem_simple_some, ← affineCoreflection_zero,
    affineCoreflection_mul_affineCoreflection]
  simp

include hθ in
/-- In type `A₁` the product of the two simple reflections has infinite order. -/
example : orderOf (b.affineWeylCoxeterSystem.simple none *
    b.affineWeylCoxeterSystem.simple (some ⟨_, hθ⟩)) = 0 := by
  rw [b.affineWeylCoxeterSystem.orderOf_simple_mul_simple,
    affineCoxeterMatrix_none_highestRoot hθ]

include hθ in
/-- In type `A₁` the translation by the coroot has length `2`. -/
example : b.affineWeylCoxeterSystem.length
    ⟨AffineEquiv.constVAdd R N (P.coroot b.highestRoot),
      P.constVAdd_coroot_mem_affineWeylGroup _⟩ = 2 := by
  rw [← constVAdd_coroot_eq_simple_mul_simple hθ]
  have hred := b.affineWeylCoxeterSystem.isReduced_alternatingWord
    (m := 2) (.inr (affineCoxeterMatrix_none_highestRoot hθ))
  simpa [CoxeterSystem.alternatingWord, CoxeterSystem.wordProd_cons] using hred.eq

end TypeA₁

end Comparison

end RootPairing.Base
