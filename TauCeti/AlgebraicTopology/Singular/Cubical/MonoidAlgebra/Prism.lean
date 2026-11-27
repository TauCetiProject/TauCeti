/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Prism
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Bimodule

/-!
# Equivariant cubical prisms

An equivariant homotopy gives a homotopy of right modules over the cubical chain algebra,
not just a homotopy of complexes over the coefficient ring. The prism uses time as its first
coordinate, before both the space and acting-monoid coordinates. Consequently it commutes
with the right chain action without a sign.

`cubicalChainModulePrism` is the degree-minus-one operator in cohomological grading. Its
boundary is the difference of the endpoint maps. `cubicalChainModulePrismLinearMap` bundles
its linearity over the acting chain algebra when every time slice is equivariant. Read on the
direct sums of chains, it fills the difference of the two ends of a homotopy on every cycle, by a
chain that every map forgetting the time of the homotopy pushes to zero
(`TauCeti.exists_cubicalChainDifferential_eq_sub_of_homotopy`).

For a monoid acting on the **left**, the prism with time as its last coordinate is the one that
commutes with the action, `cubicalChainModulePrismLast`. Moving a chain of degree `i` of the
monoid past this odd operator costs the Koszul sign `(-1) ^ i`
(`cubicalChainModulePrismLast_smul`). This is the form in which a homotopy of left modules
over the cubical chain algebra enters a tensor product over that algebra.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapters II and VII.
-/

public noncomputable section

open MulOpposite

namespace TauCeti

universe u

variable {X Y : Type u} {G : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (R : Type*) [CommRing R] {f g : C(X, Y)}

/-- The cubical prism, extended to the direct sum of all chain dimensions. -/
def cubicalChainModulePrism (H : f.Homotopy g) :
    cubicalChainModule X G R →ₗ[R] cubicalChainModule Y G R :=
  cubicalChainModuleDesc fun n ↦
    (cubicalChainModuleLof Y G R (n + 1)).comp (NormalizedCubicalChain.prism R H n)

variable {R}

/-- On a homogeneous chain the module prism is the normalized cubical prism. -/
@[simp]
theorem cubicalChainModulePrism_lof (H : f.Homotopy g) {n : ℕ}
    (c : NormalizedCubicalChain X R n) :
    cubicalChainModulePrism (G := G) R H (cubicalChainModuleLof X G R n c) =
      cubicalChainModuleLof Y G R (n + 1) (NormalizedCubicalChain.prism R H n c) :=
  cubicalChainModuleDesc_lof _ c

/-- The prism lowers cohomological degree by one. -/
theorem cubicalChainModulePrism_mem (H : f.Homotopy g) {i : ℤ}
    {x : cubicalChainModule X G R} (hx : x ∈ cubicalChainModuleGrading X G R i) :
    cubicalChainModulePrism R H x ∈ cubicalChainModuleGrading Y G R (i - 1) := by
  rcases mem_cubicalChainModuleGrading_iff.1 hx with rfl | ⟨n, c, hn, rfl⟩
  · simp only [map_zero, Submodule.zero_mem]
  · rw [cubicalChainModulePrism_lof]
    exact mem_cubicalChainModuleGrading_iff.2
      (Or.inr ⟨n + 1, _, by push_cast; omega, rfl⟩)

/-- The boundary of the module prism is the difference of the endpoint push-forwards. -/
theorem cubicalChainModuleDifferential_prism_add_prism_differential (H : f.Homotopy g)
    (x : cubicalChainModule X G R) :
    cubicalChainModuleDifferential Y G R (cubicalChainModulePrism R H x) +
        cubicalChainModulePrism R H (cubicalChainModuleDifferential X G R x) =
      cubicalChainModuleLinearMap R g x - cubicalChainModuleLinearMap R f x := by
  induction x using cubicalChainModule.induction_on with
  | add x y hx hy =>
    simp only [map_add]
    rw [add_add_add_comm, hx, hy]
    abel
  | lof n c =>
    rw [cubicalChainModulePrism_lof, cubicalChainModuleDifferential_lof_succ,
      cubicalChainModuleLinearMap_lof, cubicalChainModuleLinearMap_lof]
    cases n with
    | zero =>
      rw [cubicalChainModuleDifferential_lof_zero, map_zero, add_zero,
        NormalizedCubicalChain.boundary_prism_zero, map_sub]
    | succ n =>
      rw [cubicalChainModuleDifferential_lof_succ, cubicalChainModulePrism_lof, ← map_add,
        NormalizedCubicalChain.boundary_prism_add_prism_boundary, map_sub]

/-- **A homotopy fills the difference of its ends on cycles.** Let `H` be a homotopy from `f` to
`g` and `z` a cycle of cohomological degree `i` in `⨁ n, C^□_n(X; R)`. Some chain `c` of
cohomological degree `i - 1` has `∂ c = g_* z - f_* z`, and it is pushed to zero by any map `φ`
for which `φ ∘ H` does not depend on time: `c` is the prism of `z`, whose cubes become degenerate
in their time coordinate (`TauCeti.NormalizedCubicalChain.map_prism_eq_zero`). -/
theorem exists_cubicalChainDifferential_eq_sub_of_homotopy {Z : Type*} [TopologicalSpace Z]
    (H : f.Homotopy g) {φ : C(Y, Z)} (hφ : ∀ t x, φ (H (t, x)) = φ (H (0, x))) {i : ℤ}
    {z : normalizedCubicalChainAlgebra X R} (hz : z ∈ cubicalChainGrading X R i)
    (hdz : cubicalChainDifferential X R z = 0) :
    ∃ c ∈ cubicalChainGrading Y R (i - 1),
      cubicalChainDifferential Y R c = cubicalChainSumMap R g z - cubicalChainSumMap R f z ∧
        cubicalChainSumMap R φ c = 0 := by
  -- The prism of `z`, read on the direct sums through the module of chains with trivial action.
  set m := (cubicalChainModuleEquiv X Unit R).symm z
  have hm : cubicalChainModuleDifferential X Unit R m = 0 := by
    rw [← cubicalChainModuleEquiv_symm_differential, hdz, map_zero]
  refine ⟨cubicalChainModuleEquiv Y Unit R (cubicalChainModulePrism R H m),
    mem_cubicalChainModuleGrading.1 (cubicalChainModulePrism_mem H
      (mem_cubicalChainModuleGrading.2 (by rwa [LinearEquiv.apply_symm_apply]))), ?_, ?_⟩
  · have h := cubicalChainModuleDifferential_prism_add_prism_differential H m
    rw [hm, map_zero, add_zero] at h
    rw [← cubicalChainModuleEquiv_differential, h, map_sub, cubicalChainModuleEquiv_linearMap,
      cubicalChainModuleEquiv_linearMap, LinearEquiv.apply_symm_apply]
  · have h (a : cubicalChainModule X Unit R) :
        cubicalChainModuleLinearMap (G' := Unit) R φ (cubicalChainModulePrism R H a) = 0 := by
      induction a using cubicalChainModule.induction_on with
      | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]
      | lof n c =>
        rw [cubicalChainModulePrism_lof, cubicalChainModuleLinearMap_lof,
          NormalizedCubicalChain.map_prism_eq_zero R H hφ, map_zero]
    rw [← cubicalChainModuleEquiv_linearMap, h, map_zero]

section Action

variable [TopologicalSpace G] [SMul Gᵐᵒᵖ X] [ContinuousSMul Gᵐᵒᵖ X]
  [SMul Gᵐᵒᵖ Y] [ContinuousSMul Gᵐᵒᵖ Y]

/-- An equivariant prism commutes with the right action of homogeneous chains. The cast
only identifies the two parenthesizations of the number of coordinates. -/
theorem NormalizedCubicalChain.prism_act (H : f.Homotopy g)
    (hH : ∀ (t : unitInterval) (a : G) (x : X), H (t, op a • x) = op a • H (t, x))
    {p q : ℕ}
    (c : NormalizedCubicalChain X R p) (a : NormalizedCubicalChain G R q) :
    NormalizedCubicalChain.cast R (by omega : (p + q) + 1 = (p + 1) + q)
        (NormalizedCubicalChain.prism R H (p + q)
          (NormalizedCubicalChain.act X G R p q c a)) =
      NormalizedCubicalChain.act Y G R (p + 1) q
        (NormalizedCubicalChain.prism R H p c) a := by
  induction c using NormalizedCubicalChain.induction_on with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd, LinearMap.add_apply]
  | smul r c hc => simp only [map_smul, hc, LinearMap.smul_apply]
  | ofCube c =>
    induction a using NormalizedCubicalChain.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | smul r a ha => simp only [map_smul, ha]
    | ofCube a =>
      simp only [NormalizedCubicalChain.act_def, NormalizedCubicalChain.crossProduct_ofCube,
        NormalizedCubicalChain.map_ofCube, NormalizedCubicalChain.prism_ofCube,
        map_neg, LinearMap.neg_apply]
      congr 1
      rw [NormalizedCubicalChain.cast_ofCube]
      apply congrArg (NormalizedCubicalChain.ofCube Y R)
      ext x
      simp only [SingularCube.cast_apply, SingularCube.prism_apply,
        ContinuousMap.comp_apply, SingularCube.crossProduct_apply, actMap_apply, hH]
      congr 3
      funext i
      simp only [Fin.tail, Function.comp_def]
      congr 1
      apply Fin.ext
      simp
      omega

end Action

section MonoidAction

variable [Monoid G] [TopologicalSpace G] [ContinuousMul G]
  [MulAction Gᵐᵒᵖ X] [ContinuousSMul Gᵐᵒᵖ X]
  [MulAction Gᵐᵒᵖ Y] [ContinuousSMul Gᵐᵒᵖ Y]

/-- The prism of an equivariant homotopy is linear over the right chain-algebra action. -/
theorem cubicalChainModulePrism_op_smul (H : f.Homotopy g)
    (hH : ∀ (t : unitInterval) (a : G) (x : X), H (t, op a • x) = op a • H (t, x))
    (a : normalizedCubicalChainAlgebra G R) (x : cubicalChainModule X G R) :
    cubicalChainModulePrism R H (op a • x) = op a • cubicalChainModulePrism R H x := by
  induction x using cubicalChainModule.induction_on with
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | lof p c =>
    induction a using DirectSum.induction_on with
    | zero => simp
    | add a b ha hb => simp only [op_add, add_smul, map_add, ha, hb]
    | of q a =>
      rw [← DirectSum.lof_eq_of R, op_lof_smul_cubicalChainModuleLof,
        cubicalChainModulePrism_lof, cubicalChainModulePrism_lof,
        op_lof_smul_cubicalChainModuleLof, ← NormalizedCubicalChain.prism_act H hH,
        cubicalChainModuleLof_cast]

/-- The prism of an equivariant homotopy as a right chain-algebra linear map. It has
cohomological degree minus one, rather than being a morphism of DG modules. -/
def cubicalChainModulePrismLinearMap (H : f.Homotopy g)
    (hH : ∀ (t : unitInterval) (a : G) (x : X), H (t, op a • x) = op a • H (t, x)) :
    cubicalChainModule X G R →ₗ[(normalizedCubicalChainAlgebra G R)ᵐᵒᵖ]
      cubicalChainModule Y G R where
  toFun := cubicalChainModulePrism R H
  map_add' := map_add _
  map_smul' a x := by
    rw [← op_unop a]
    exact cubicalChainModulePrism_op_smul H hH a.unop x

/-- The bundled equivariant prism has the same values as the coefficient-linear prism. -/
@[simp]
theorem cubicalChainModulePrismLinearMap_apply (H : f.Homotopy g)
    (hH : ∀ (t : unitInterval) (a : G) (x : X), H (t, op a • x) = op a • H (t, x))
    (x : cubicalChainModule X G R) :
    cubicalChainModulePrismLinearMap H hH x = cubicalChainModulePrism R H x := (rfl)

end MonoidAction

section LeftAction

variable {L : Type*} [TopologicalSpace L] [SMul L X] [ContinuousSMul L X] [SMul L Y]
  [ContinuousSMul L Y]

/-- The prism with time last of an equivariant homotopy commutes with the left action, up to the
Koszul sign `(-1) ^ p` of a `p`-chain passing the operator. The cast only identifies the two
parenthesizations of the number of coordinates. -/
theorem NormalizedCubicalChain.prismLast_leftAct (H : f.Homotopy g)
    (hH : ∀ (t : unitInterval) (a : L) (x : X), H (t, a • x) = a • H (t, x)) {p q : ℕ}
    (a : NormalizedCubicalChain L R p) (c : NormalizedCubicalChain X R q) :
    NormalizedCubicalChain.cast R (by omega : (p + q) + 1 = p + (q + 1))
        (NormalizedCubicalChain.prismLast R H (p + q)
          (NormalizedCubicalChain.leftAct L X R p q a c)) =
      ((-1 : ℤ) ^ p) • NormalizedCubicalChain.leftAct L Y R p (q + 1) a
        (NormalizedCubicalChain.prismLast R H q c) := by
  induction c using NormalizedCubicalChain.induction_on with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd, smul_add]
  | smul r c hc => simp only [map_smul, hc, smul_comm r]
  | ofCube c =>
    induction a using NormalizedCubicalChain.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb, LinearMap.add_apply, smul_add]
    | smul r a ha => simp only [map_smul, ha, LinearMap.smul_apply, smul_comm r]
    | ofCube a =>
      simp only [NormalizedCubicalChain.leftAct_ofCube, NormalizedCubicalChain.prismLast_ofCube,
        map_zsmul, smul_smul, ← pow_add]
      -- Reassociate only the sign exponent: the cast also depends on `p + q + 1`.
      rw (occs := .pos [1]) [add_assoc]
      congr 1
      rw [NormalizedCubicalChain.cast_ofCube]
      apply congrArg (NormalizedCubicalChain.ofCube Y R)
      ext x
      simp only [SingularCube.cast_apply, SingularCube.prismLast_apply,
        ContinuousMap.comp_apply, SingularCube.crossProduct_apply, leftActMap_apply, hH]
      -- Both sides read the same coordinates of `x`, split before and after the cast.
      have ha : (fun i ↦ Fin.init (x ∘ Fin.cast (by omega)) (Fin.castAdd q i)) =
          fun i ↦ x (Fin.castAdd (q + 1) i) :=
        funext fun i ↦ congrArg x (Fin.ext (by simp))
      have ht : (x ∘ Fin.cast (by omega)) (Fin.last (p + q)) = x (Fin.natAdd p (Fin.last q)) :=
        congrArg x (Fin.ext (by simp))
      have hc : (fun j ↦ Fin.init (x ∘ Fin.cast (by omega)) (Fin.natAdd p j)) =
          Fin.init fun j ↦ x (Fin.natAdd p j) :=
        funext fun j ↦ congrArg x (Fin.ext (by simp))
      rw [ha, ht, hc]

end LeftAction

section PrismLast

variable (R) in
/-- The cubical prism with time last, extended to the direct sum of all chain dimensions. -/
def cubicalChainModulePrismLast (H : f.Homotopy g) :
    cubicalChainModule X G R →ₗ[R] cubicalChainModule Y G R :=
  cubicalChainModuleDesc fun n ↦
    (cubicalChainModuleLof Y G R (n + 1)).comp (NormalizedCubicalChain.prismLast R H n)

/-- On a homogeneous chain the module prism with time last is the normalized one. -/
@[simp]
theorem cubicalChainModulePrismLast_lof (H : f.Homotopy g) {n : ℕ}
    (c : NormalizedCubicalChain X R n) :
    cubicalChainModulePrismLast (G := G) R H (cubicalChainModuleLof X G R n c) =
      cubicalChainModuleLof Y G R (n + 1) (NormalizedCubicalChain.prismLast R H n c) :=
  cubicalChainModuleDesc_lof _ c

/-- The prism with time last lowers cohomological degree by one. -/
theorem cubicalChainModulePrismLast_mem (H : f.Homotopy g) {i : ℤ}
    {x : cubicalChainModule X G R} (hx : x ∈ cubicalChainModuleGrading X G R i) :
    cubicalChainModulePrismLast R H x ∈ cubicalChainModuleGrading Y G R (i - 1) := by
  rcases mem_cubicalChainModuleGrading_iff.1 hx with rfl | ⟨n, c, hn, rfl⟩
  · simp only [map_zero, Submodule.zero_mem]
  · rw [cubicalChainModulePrismLast_lof]
    exact mem_cubicalChainModuleGrading_iff.2
      (Or.inr ⟨n + 1, _, by push_cast; omega, rfl⟩)

/-- The boundary of the module prism with time last is the difference of the endpoint
push-forwards. -/
theorem cubicalChainModuleDifferential_prismLast_add_prismLast_differential (H : f.Homotopy g)
    (x : cubicalChainModule X G R) :
    cubicalChainModuleDifferential Y G R (cubicalChainModulePrismLast R H x) +
        cubicalChainModulePrismLast R H (cubicalChainModuleDifferential X G R x) =
      cubicalChainModuleLinearMap R g x - cubicalChainModuleLinearMap R f x := by
  induction x using cubicalChainModule.induction_on with
  | add x y hx hy =>
    simp only [map_add]
    rw [add_add_add_comm, hx, hy]
    abel
  | lof n c =>
    rw [cubicalChainModulePrismLast_lof, cubicalChainModuleDifferential_lof_succ,
      cubicalChainModuleLinearMap_lof, cubicalChainModuleLinearMap_lof]
    cases n with
    | zero =>
      rw [cubicalChainModuleDifferential_lof_zero, map_zero, add_zero,
        NormalizedCubicalChain.boundary_prismLast_zero, map_sub]
    | succ n =>
      rw [cubicalChainModuleDifferential_lof_succ, cubicalChainModulePrismLast_lof, ← map_add,
        NormalizedCubicalChain.boundary_prismLast_add_prismLast_boundary, map_sub]

end PrismLast

section LeftMonoidAction

variable {L : Type*} [Monoid L] [TopologicalSpace L] [ContinuousMul L] [MulAction L X]
  [ContinuousSMul L X] [MulAction L Y] [ContinuousSMul L Y]

/-- **The prism with time last of an equivariant homotopy is graded linear for the left
action**: a chain of cohomological degree `i` passes it with the Koszul sign `(-1) ^ i`, since
the operator has odd degree. -/
theorem cubicalChainModulePrismLast_smul (H : f.Homotopy g)
    (hH : ∀ (t : unitInterval) (a : L) (x : X), H (t, a • x) = a • H (t, x)) {i : ℤ}
    {a : normalizedCubicalChainAlgebra L R} (ha : a ∈ cubicalChainGrading L R i)
    (x : cubicalChainModule X G R) :
    cubicalChainModulePrismLast R H (a • x) =
      i.negOnePow • (a • cubicalChainModulePrismLast R H x) := by
  rcases (mem_cubicalChainGrading_iff L R).1 ha with rfl | ⟨p, y, hp, rfl⟩
  · simp
  obtain rfl : i = -(p : ℤ) := by omega
  induction x using cubicalChainModule.induction_on with
  | add x x' hx hx' => rw [smul_add, map_add, hx, hx', map_add, smul_add, smul_add]
  | lof q c =>
    rw [lof_smul_cubicalChainModuleLof, cubicalChainModulePrismLast_lof,
      cubicalChainModulePrismLast_lof, lof_smul_cubicalChainModuleLof,
      ← cubicalChainModuleLof_cast (by omega : p + q + 1 = p + (q + 1)),
      NormalizedCubicalChain.prismLast_leftAct H hH, map_zsmul,
      negOnePow_neg_natCast_smul_cubicalChainModule, ← Int.cast_smul_eq_zsmul R]
    simp

end LeftMonoidAction

end TauCeti
