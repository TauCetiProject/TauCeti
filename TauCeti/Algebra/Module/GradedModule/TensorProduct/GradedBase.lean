/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Algebra.GradedMulAction
public import TauCeti.Algebra.Module.GradedModule.Quotient
public import TauCeti.Algebra.Module.GradedModule.TensorProduct.Basic

/-!
# Tensor products over a graded commutative ring

Let `A` be a commutative `k`-algebra with a decomposition `𝒜 : ι → Submodule k A`, indexed by
an additive commutative monoid `ι`, and let `M` and `N` be `A`-modules with internal gradings
`G` and `H` by `k`-submodules on which `𝒜` acts homogeneously. The tensor product `M ⊗[A] N`
over `A` is then graded by total degree: its degree-`d` piece is spanned by the pure tensors
`m ⊗ₜ n` with `m` of degree `p`, `n` of degree `q` and `p + q = d`. The degree pieces are
`k`-submodules; they need not be `A`-submodules, since multiplication by an element of `𝒜 i`
moves degree `d` to degree `i + d`.

The grading is the image of the total-degree grading `InternalGrading.tensorProduct` of
`M ⊗[k] N` under the canonical surjection `TensorProduct.mapOfCompatibleSMul` onto `M ⊗[A] N`.
The images are independent because the kernel of this surjection is homogeneous: on a
balancing relation `(a • m) ⊗ n - m ⊗ (a • n)` with `a`, `m` and `n` homogeneous, both terms have
degree `|a| + |m| + |n|`. No flatness or finiteness hypothesis is needed, and the actions
introduce no Koszul sign.

This is the tensor product of graded modules over a graded commutative ring, such as a ring of
symmetric polynomials with its weighted grading, used for graded state spaces and graded
hom-modules.

## Main definitions

* `TauCeti.InternalGrading.tensorProductOver`: the total-degree grading of `M ⊗[A] N`.

## Main results

* `TauCeti.InternalGrading.tensorProductOver_piece`: a degree piece is the image of the
  corresponding piece of `M ⊗[k] N`.
* `TauCeti.InternalGrading.tmul_mem_tensorProductOver`: degrees add on pure tensors.
* `TauCeti.InternalGrading.tensorProductOver_piece_le_of_add_eq`: a submodule containing the
  homogeneous pure tensors of total degree `d` contains the degree-`d` piece.
* `TauCeti.InternalGrading.isHomogeneous_of_tmul_mem_tensorProductOver`: homogeneity of a map
  out of `M ⊗[A] N` can be checked on homogeneous pure tensors.
* `LinearMap.IsHomogeneous.tensorProductOver`: tensoring homogeneous `A`-linear maps adds
  their degrees.
* `TauCeti.InternalGrading.isHomogeneous_comm_tensorProductOver` and
  `TauCeti.InternalGrading.isHomogeneous_assoc_tensorProductOver`: the symmetry and associativity
  isomorphisms preserve total degree.
* `TauCeti.InternalGrading.isHomogeneous_lid_tensorProductOver` and
  `TauCeti.InternalGrading.isHomogeneous_rid_tensorProductOver`: so do the unit isomorphisms
  with the regular module `A`.
* `TauCeti.InternalGrading.gradedSMul_tensorProductOver`: `𝒜` acts homogeneously on the
  tensor product.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Lecture Notes in Mathematics
  1836, Chapter 2.
-/

public section

open DirectSum TensorProduct

namespace TauCeti

variable {k A M N ι : Type*} [CommRing k] [CommRing A] [Algebra k A]
  [DecidableEq ι] [AddCommMonoid ι] (𝒜 : ι → Submodule k A) [Decomposition 𝒜]
  [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
  (G : InternalGrading k M ι) (H : InternalGrading k N ι)
  [SetLike.GradedSMul 𝒜 G.piece] [SetLike.GradedSMul 𝒜 H.piece]

namespace InternalGrading

section Kernel

/-- The degree-`d` component of a pure tensor over `k`, viewed in `M ⊗[A] N`, as an
additive function of both factors. -/
private noncomputable def tensorComponent (d : ι) : M →+ N →+ M ⊗[A] N :=
  LinearMap.toAddMonoidHom'.comp
    ((TensorProduct.mk k M N).compr₂
      (mapOfCompatibleSMul A k k M N ∘ₗ ((G.tensorProduct H).piece d).subtype ∘ₗ
        DirectSum.component k ι (fun p ↦ (G.tensorProduct H).piece p) d ∘ₗ
          (decomposeLinearEquiv (G.tensorProduct H).piece).toLinearMap)).toAddMonoidHom

private theorem tensorComponent_apply (d : ι) (m : M) (n : N) :
    tensorComponent (A := A) G H d m n =
      mapOfCompatibleSMul A k k M N (decompose (G.tensorProduct H).piece (m ⊗ₜ[k] n) d) :=
  (rfl)

include 𝒜 in
/-- The component map of `tensorComponent` is balanced over `A`: both terms of a balancing
relation on homogeneous inputs have the same total degree. -/
private theorem tensorComponent_smul (d : ι) (a : A) (m : M) (n : N) :
    tensorComponent G H d (a • m) n = tensorComponent (A := A) G H d m (a • n) := by
  classical
  induction a using Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add a a' ha ha' => simp only [add_smul, map_add, AddMonoidHom.add_apply, ha, ha']
  | @homogeneous i a =>
  induction m using Decomposition.inductionOn G.piece with
  | zero => simp
  | add m m' hm hm' => simp only [smul_add, map_add, AddMonoidHom.add_apply, hm, hm']
  | @homogeneous p m =>
  induction n using Decomposition.inductionOn H.piece with
  | zero => simp
  | add n n' hn hn' => simp only [smul_add, map_add, hn, hn']
  | @homogeneous q n =>
  have h₁ : ((a : A) • (m : M)) ⊗ₜ[k] (n : N) ∈ (G.tensorProduct H).piece (i + p + q) :=
    G.tmul_mem_tensorProduct H (SetLike.GradedSMul.smul_mem a.property m.property) n.property
  have h₂ : (m : M) ⊗ₜ[k] ((a : A) • (n : N)) ∈ (G.tensorProduct H).piece (i + p + q) := by
    rw [add_assoc, add_left_comm]
    exact G.tmul_mem_tensorProduct H m.property (SetLike.GradedSMul.smul_mem a.property n.property)
  rw [tensorComponent_apply, tensorComponent_apply]
  by_cases hd : i + p + q = d
  · subst hd
    rw [decompose_of_mem_same _ h₁, decompose_of_mem_same _ h₂, mapOfCompatibleSMul_tmul,
      mapOfCompatibleSMul_tmul, smul_tmul]
  · rw [decompose_of_mem_ne _ h₁ hd, decompose_of_mem_ne _ h₂ hd]

/-- The homogeneous projection of `M ⊗[A] N` induced from that of `M ⊗[k] N`. -/
private noncomputable def tensorProj (d : ι) : M ⊗[A] N →+ M ⊗[A] N :=
  liftAddHom (tensorComponent G H d) (tensorComponent_smul 𝒜 G H d)

private theorem mapOfCompatibleSMul_decompose (d : ι) (z : M ⊗[k] N) :
    mapOfCompatibleSMul A k k M N (decompose (G.tensorProduct H).piece z d) =
      tensorProj 𝒜 G H d (mapOfCompatibleSMul A k k M N z) := by
  induction z using TensorProduct.inductionOn with
  | tmul m n =>
    rw [mapOfCompatibleSMul_tmul, tensorProj, liftAddHom_tmul, tensorComponent_apply]
  | add x y hx hy =>
    simp only [decompose_add, DirectSum.add_apply, Submodule.coe_add, map_add, hx, hy]

include 𝒜 in
/-- The kernel of the canonical surjection `M ⊗[k] N → M ⊗[A] N` is homogeneous for the
total-degree grading. -/
theorem isHomogeneous_ker_mapOfCompatibleSMul :
    SetLike.IsHomogeneous (G.tensorProduct H).piece
      (LinearMap.ker (mapOfCompatibleSMul A k k M N)) := fun d z hz ↦ by
  rw [LinearMap.mem_ker] at hz ⊢
  rw [mapOfCompatibleSMul_decompose 𝒜, hz, map_zero]

end Kernel

/-- The total-degree grading of the tensor product `M ⊗[A] N` over a graded commutative ring:
the degree-`d` piece is spanned by the pure tensors of homogeneous elements whose degrees sum
to `d`. The decomposition `𝒜` of `A` enters only through the homogeneity of the balancing
relations. -/
noncomputable def tensorProductOver : InternalGrading k (M ⊗[A] N) ι :=
  ((G.tensorProduct H).quotient _ (isHomogeneous_ker_mapOfCompatibleSMul 𝒜 G H)).map
    ((mapOfCompatibleSMul A k k M N).quotKerEquivOfSurjective
      (mapOfCompatibleSMul_surjective A k k M N))

/-- A degree piece of the tensor product over `A` is the image of the corresponding degree
piece of the tensor product over `k`. -/
theorem tensorProductOver_piece (d : ι) :
    (G.tensorProductOver 𝒜 H).piece d =
      ((G.tensorProduct H).piece d).map (mapOfCompatibleSMul A k k M N) := by
  rw [tensorProductOver, map_piece, quotient_piece, ← Submodule.map_comp]
  -- The composite sends `x` to the class of `x` and then to `mapOfCompatibleSMul x`; Mathlib
  -- proves this pointwise identity `LinearMap.quotKerEquivOfSurjective_apply_mk` by `rfl`.
  rfl

/-- An element of `M ⊗[A] N` has degree `d` exactly when it is the image of an element of
`M ⊗[k] N` of degree `d`. -/
theorem mem_tensorProductOver_piece_iff {d : ι} {z : M ⊗[A] N} :
    z ∈ (G.tensorProductOver 𝒜 H).piece d ↔
      ∃ x ∈ (G.tensorProduct H).piece d, mapOfCompatibleSMul A k k M N x = z := by
  rw [tensorProductOver_piece, Submodule.mem_map]

/-- A pure tensor of elements of degrees `p` and `q` has degree `p + q`. -/
theorem tmul_mem_tensorProductOver {p q : ι} {m : M} {n : N} (hm : m ∈ G.piece p)
    (hn : n ∈ H.piece q) : m ⊗ₜ[A] n ∈ (G.tensorProductOver 𝒜 H).piece (p + q) :=
  (G.mem_tensorProductOver_piece_iff 𝒜 H).2
    ⟨_, G.tmul_mem_tensorProduct H hm hn, mapOfCompatibleSMul_tmul _ _ _ _ _ m n⟩

/-- A `k`-submodule containing every pure tensor of homogeneous elements whose degrees sum to
`d` contains the degree-`d` piece. -/
theorem tensorProductOver_piece_le_of_add_eq {d : ι} {C : Submodule k (M ⊗[A] N)}
    (h : ∀ p q : ι, p + q = d → ∀ m ∈ G.piece p, ∀ n ∈ H.piece q, m ⊗ₜ[A] n ∈ C) :
    (G.tensorProductOver 𝒜 H).piece d ≤ C := by
  rw [tensorProductOver_piece, Submodule.map_le_iff_le_comap]
  exact G.tensorProduct_piece_le_of_add_eq H fun p q hpq m hm n hn ↦ h p q hpq m hm n hn

/-- An `A`-linear map out of `M ⊗[A] N` that shifts the degree of every homogeneous pure tensor
by `s` is homogeneous of degree `s`. -/
theorem isHomogeneous_of_tmul_mem_tensorProductOver {Q : Type*} [AddCommMonoid Q] [Module k Q]
    [Module A Q] [IsScalarTower k A Q] (𝓠 : ι → Submodule k Q) (f : M ⊗[A] N →ₗ[A] Q) (s : ι)
    (hf : ∀ {p q : ι} {m : M} {n : N}, m ∈ G.piece p → n ∈ H.piece q →
      f (m ⊗ₜ[A] n) ∈ 𝓠 (p + q + s)) :
    LinearMap.IsHomogeneous f (G.tensorProductOver 𝒜 H).piece 𝓠 s :=
  LinearMap.isHomogeneous_def.2 fun d _ hz ↦
    (G.tensorProductOver_piece_le_of_add_eq 𝒜 H (C := (𝓠 (d + s)).comap (f.restrictScalars k))
      fun p q hpq _ hm _ hn ↦ by
        simpa only [Submodule.mem_comap, LinearMap.restrictScalars_apply, ← hpq] using hf hm hn) hz

/-- The decomposition `𝒜` acts homogeneously on the tensor product over `A`. -/
instance gradedSMul_tensorProductOver :
    SetLike.GradedSMul 𝒜 (G.tensorProductOver 𝒜 H).piece where
  smul_mem {i d} a z ha hz := by
    rw [vadd_eq_add, add_comm]
    refine (G.isHomogeneous_of_tmul_mem_tensorProductOver 𝒜 H _ (LinearMap.lsmul A _ a) i
      fun {p q m n} hm hn ↦ ?_).map_mem hz
    rw [LinearMap.lsmul_apply, smul_tmul', add_comm (p + q), ← add_assoc]
    exact G.tmul_mem_tensorProductOver 𝒜 H (SetLike.GradedSMul.smul_mem ha hm) hn

section Assoc

variable {P : Type*} [AddCommGroup P] [Module k P] [Module A P] [IsScalarTower k A P]
  (K : InternalGrading k P ι) [SetLike.GradedSMul 𝒜 K.piece]

/-- The symmetry `m ⊗ n ↦ n ⊗ m` of the tensor product over `A` preserves total degree. No Koszul
sign is introduced. -/
theorem isHomogeneous_comm_tensorProductOver :
    LinearMap.IsHomogeneous (TensorProduct.comm A M N).toLinearMap
      (G.tensorProductOver 𝒜 H).piece (H.tensorProductOver 𝒜 G).piece 0 :=
  G.isHomogeneous_of_tmul_mem_tensorProductOver 𝒜 H _ _ _ fun {p q _ _} hm hn ↦ by
    rw [LinearEquiv.coe_coe, comm_tmul, add_zero, add_comm]
    exact H.tmul_mem_tensorProductOver 𝒜 G hn hm

/-- Reassociating a triple tensor product over `A` preserves total degree. -/
theorem isHomogeneous_assoc_tensorProductOver :
    LinearMap.IsHomogeneous (TensorProduct.assoc A M N P).toLinearMap
      ((G.tensorProductOver 𝒜 H).tensorProductOver 𝒜 K).piece
      (G.tensorProductOver 𝒜 (H.tensorProductOver 𝒜 K)).piece 0 :=
  (G.tensorProductOver 𝒜 H).isHomogeneous_of_tmul_mem_tensorProductOver 𝒜 K _ _ _
    fun {p q x r} hx hr ↦ by
      -- Fix the third factor `r` and check the first factor on homogeneous pure tensors.
      let f : M ⊗[A] N →ₗ[A] M ⊗[A] (N ⊗[A] P) :=
        (TensorProduct.assoc A M N P).toLinearMap ∘ₗ (TensorProduct.mk A (M ⊗[A] N) P).flip r
      rw [add_zero]
      refine (G.isHomogeneous_of_tmul_mem_tensorProductOver 𝒜 H _ f q
        fun {p₁ p₂ m n} hm hn ↦ ?_).map_mem hx
      rw [LinearMap.comp_apply, LinearMap.flip_apply, mk_apply, LinearEquiv.coe_coe, assoc_tmul,
        add_assoc]
      exact G.tmul_mem_tensorProductOver 𝒜 _ hm (H.tmul_mem_tensorProductOver 𝒜 K hn hr)

end Assoc

section Unit

variable [SetLike.GradedMul 𝒜]

/-- The left unit isomorphism `A ⊗[A] M ≃ M`, `a ⊗ m ↦ a • m`, preserves total degree. -/
theorem isHomogeneous_lid_tensorProductOver :
    LinearMap.IsHomogeneous (TensorProduct.lid A M).toLinearMap
      ((ofDecomposition 𝒜).tensorProductOver 𝒜 G).piece G.piece 0 :=
  (ofDecomposition 𝒜).isHomogeneous_of_tmul_mem_tensorProductOver 𝒜 G _ _ _
    fun {p q a m} ha hm ↦ by
      rw [ofDecomposition_piece] at ha
      rw [LinearEquiv.coe_coe, lid_tmul, add_zero]
      exact SetLike.GradedSMul.smul_mem ha hm

/-- The right unit isomorphism `M ⊗[A] A ≃ M`, `m ⊗ a ↦ a • m`, preserves total degree. -/
theorem isHomogeneous_rid_tensorProductOver :
    LinearMap.IsHomogeneous (TensorProduct.rid A M).toLinearMap
      (G.tensorProductOver 𝒜 (ofDecomposition 𝒜)).piece G.piece 0 :=
  G.isHomogeneous_of_tmul_mem_tensorProductOver 𝒜 (ofDecomposition 𝒜) _ _ _
    fun {p q m a} hm ha ↦ by
      rw [ofDecomposition_piece] at ha
      rw [LinearEquiv.coe_coe, rid_tmul, add_zero, add_comm]
      exact SetLike.GradedSMul.smul_mem ha hm

end Unit

end InternalGrading

section IsHomogeneous

variable {G H} {M' N' : Type*}
  [AddCommGroup M'] [Module k M'] [Module A M'] [IsScalarTower k A M']
  [AddCommGroup N'] [Module k N'] [Module A N'] [IsScalarTower k A N']
  {G' : InternalGrading k M' ι} {H' : InternalGrading k N' ι}
  [SetLike.GradedSMul 𝒜 G'.piece] [SetLike.GradedSMul 𝒜 H'.piece]
  {f : M →ₗ[A] M'} {g : N →ₗ[A] N'}

/-- Tensoring `A`-linear maps of degrees `s` and `t` gives a map of degree `s + t` for the
total-degree gradings over `A`. -/
theorem _root_.LinearMap.IsHomogeneous.tensorProductOver {s t : ι}
    (hf : LinearMap.IsHomogeneous f G.piece G'.piece s)
    (hg : LinearMap.IsHomogeneous g H.piece H'.piece t) :
    LinearMap.IsHomogeneous (TensorProduct.map f g)
      (G.tensorProductOver 𝒜 H).piece (G'.tensorProductOver 𝒜 H').piece (s + t) :=
  G.isHomogeneous_of_tmul_mem_tensorProductOver 𝒜 H _ _ _ fun {p q _ _} hm hn ↦ by
    rw [map_tmul, add_add_add_comm]
    exact G'.tmul_mem_tensorProductOver 𝒜 H' (hf.map_mem hm) (hg.map_mem hn)

/-- Tensoring `A`-linear maps of degree zero gives a map of degree zero for the total-degree
gradings over `A`. -/
theorem _root_.LinearMap.IsHomogeneous.tensorProductOver_zero
    (hf : LinearMap.IsHomogeneous f G.piece G'.piece 0)
    (hg : LinearMap.IsHomogeneous g H.piece H'.piece 0) :
    LinearMap.IsHomogeneous (TensorProduct.map f g)
      (G.tensorProductOver 𝒜 H).piece (G'.tensorProductOver 𝒜 H').piece 0 := by
  simpa only [add_zero] using hf.tensorProductOver 𝒜 hg

end IsHomogeneous

end TauCeti
