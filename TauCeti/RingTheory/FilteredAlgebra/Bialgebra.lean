/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.GroupLike
public import Mathlib.RingTheory.Bialgebra.Hom
public import Mathlib.RingTheory.Bialgebra.Primitive
public import TauCeti.RingTheory.FilteredAlgebra.Exp.Map
public import TauCeti.RingTheory.FilteredAlgebra.TensorProduct.Map

/-!
# Completed coproducts, group-like elements, and primitives in filtered bialgebras

When an ideal filtration `F` on an `R`-bialgebra `A` satisfies `AlgFiltration.IsBialgFiltration`,
comultiplication and counit extend to `R`-algebra homomorphisms `AlgFiltration.completedCoproduct`
and `AlgFiltration.completedCounit` on `F.completion`. Group-like and primitive elements are defined
directly in the completion by `ε̂(x) = 1`, `Δ̂(x) = x ⊗̂ x` (`AlgFiltration.IsCompletedGroupLike`)
and `Δ̂(x) = x ⊗̂ 1 + 1 ⊗̂ x` (`AlgFiltration.IsCompletedPrimitive`). Over a rational algebra,
`AlgFiltration.completedExp` and `AlgFiltration.completedLog` restrict to inverse bijections between
completed primitive elements of `F.completionIdeal 1` and completed group-like elements congruent to
`1` modulo `F.completionIdeal 1` (and all such elements when `ker ε ≤ F.ideal 1`).

## Main definitions

* `TauCeti.AlgFiltration.IsBialgFiltration`: filtration compatibility with comultiplication/counit.
* `TauCeti.AlgFiltration.completedCoproduct`, `TauCeti.AlgFiltration.completedCounit`: induced maps
  on `F.completion`.
* `TauCeti.AlgFiltration.IsCompletedGroupLike`, `TauCeti.AlgFiltration.IsCompletedPrimitive`:
  group-like and primitive predicates in `F.completion`.
* `TauCeti.AlgFiltration.completedGroupLikeSubgroup`,
  `TauCeti.AlgFiltration.completedPrimitiveSubmodule`: unit subgroup and `R`-submodule.
* `TauCeti.AlgFiltration.completedPrimitiveCompletionIdealEquivGroupLike`,
  `TauCeti.AlgFiltration.completedPrimitiveEquivGroupLike`: exponential-logarithm bijections.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters 1–3, Ch. II, §6.
* `Mathlib/RingTheory/{Coalgebra,Bialgebra}/{GroupLike,Primitive}.lean` (`IsGroupLikeElem`,
  `Bialgebra.groupLikeSubmonoid`, `Bialgebra.IsPrimitiveElem`, `Coalgebra.IsSkewPrimitiveElem`).
-/

public section

open scoped TensorProduct

namespace TauCeti.AlgFiltration

/-- An algebra filtration on an `R`-bialgebra is a *bialgebra filtration* when comultiplication
preserves filtration order against the total-degree tensor filtration and the counit vanishes on
the first filtration ideal. -/
class IsBialgFiltration (R : Type*) {A : Type*} [CommSemiring R] [Semiring A]
    [Bialgebra R A] (F : AlgFiltration A) : Prop where
  /-- Comultiplication carries filtration order `k` into total tensor filtration order `k`. -/
  ideal_le_comap_comul (k : ℕ) :
    F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A)
  /-- The counit vanishes on the first filtration ideal. -/
  ideal_one_le_ker_counit :
    F.ideal 1 ≤ RingHom.ker (Bialgebra.counitAlgHom R A)

section Completion

variable (R : Type*) {A : Type*} [CommRing R] [Ring A] [Bialgebra R A]
  (F : AlgFiltration A) [F.IsBialgFiltration R]

/-- The completed coproduct `Δ̂ : F.completion →ₐ[R] (F.tensorProduct R F).completion`. -/
noncomputable def completedCoproduct : F.completion →ₐ[R] (F.tensorProduct R F).completion :=
  F.mapCompletionₐ (F.tensorProduct R F) (Bialgebra.comulAlgHom R A) id monotone_id
    fun k => IsBialgFiltration.ideal_le_comap_comul (R := R) (F := F) (k + 1)

/-- At order `k`, `completedCoproduct` is induced on `A ⧸ F.ideal (k + 1)` by `comulAlgHom`. -/
@[simp] theorem projection_completedCoproduct (k : ℕ) (x : F.completion) :
    (F.tensorProduct R F).projection k (F.completedCoproduct R x) =
      Ideal.quotientMapₐ ((F.tensorProduct R F).ideal (k + 1)) (Bialgebra.comulAlgHom R A)
        (IsBialgFiltration.ideal_le_comap_comul (R := R) (F := F) (k + 1)) (F.projection k x) :=
  F.projection_mapCompletionₐ _ _ _ monotone_id _ k x

/-- On canonical images of elements of `A`, `completedCoproduct` agrees with `Coalgebra.comul`. -/
@[simp] theorem completedCoproduct_toCompletion (a : A) :
    F.completedCoproduct R (F.toCompletion a) =
      (F.tensorProduct R F).toCompletion (Coalgebra.comul (R := R) a) :=
  F.mapCompletionₐ_toCompletion _ _ _ monotone_id _ a

/-- The completed coproduct preserves every filtration order. -/
theorem completedCoproduct_mem_completionIdeal {k : ℕ} {x : F.completion}
    (hx : x ∈ F.completionIdeal k) :
    F.completedCoproduct R x ∈ (F.tensorProduct R F).completionIdeal k :=
  match k with
  | 0 => by simp
  | k + 1 => F.mapCompletionₐ_mem_completionIdeal _ _ id monotone_id _ k hx

/-- When `A` is cocommutative, `completedCoproduct` is invariant under completed factor exchange. -/
@[simp] theorem completedTensorComm_completedCoproduct [Coalgebra.IsCocomm R A] (x : F.completion) :
    F.completedTensorComm R F (F.completedCoproduct R x) = F.completedCoproduct R x := by
  refine (F.tensorProduct R F).completion_ext fun k => ?_
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (F.projection k x)
  rw [projection_completedTensorComm, projection_completedCoproduct, ← ha]
  simp only [Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk, AlgEquiv.coe_toAlgHom,
    Bialgebra.comulAlgHom_apply]
  congr 1
  simpa only [← AlgEquiv.toLinearEquiv_apply, Algebra.TensorProduct.comm_toLinearEquiv,
    LinearMap.comp_apply, LinearEquiv.coe_coe] using
    LinearMap.congr_fun (Coalgebra.comm_comp_comul R A) a

/-- The completed counit `ε̂ : F.completion →ₐ[R] R` induced through `A ⧸ F.ideal 1`. -/
noncomputable def completedCounit : F.completion →ₐ[R] R :=
  (Ideal.Quotient.liftₐ (F.ideal 1) (Bialgebra.counitAlgHom R A)
    fun _ ha => RingHom.mem_ker.mp (IsBialgFiltration.ideal_one_le_ker_counit ha)).comp
    (F.projectionₐ (R := R) 0)

/-- Any representative of the order-zero projection computes the completed counit. -/
theorem completedCounit_of_representative (x : F.completion) (a : A)
    (ha : Ideal.Quotient.mk (F.ideal 1) a = F.projection 0 x) :
    F.completedCounit R x = Coalgebra.counit (R := R) a := by
  simp only [completedCounit, AlgHom.comp_apply, projectionₐ_apply, ← ha]; rfl

/-- On canonical images of elements of `A`, `completedCounit` agrees with `Coalgebra.counit`. -/
@[simp] theorem completedCounit_toCompletion (a : A) :
    F.completedCounit R (F.toCompletion a) = Coalgebra.counit (R := R) a :=
  F.completedCounit_of_representative R (F.toCompletion a) a (F.projection_toCompletion 0 a).symm

/-- The completed counit vanishes on `F.completionIdeal 1`. -/
theorem completedCounit_eq_zero_of_mem {x : F.completion} (hx : x ∈ F.completionIdeal 1) :
    F.completedCounit R x = 0 := by
  have hx0 : F.projection 0 x = 0 := by simpa only [completionIdeal_succ, RingHom.mem_ker] using hx
  simp [completedCounit, hx0]

/-- Elements congruent to `1` modulo `F.completionIdeal 1` have completed counit `1`. -/
theorem completedCounit_eq_one_of_sub_one_mem {u : F.completion}
    (hu : u - 1 ∈ F.completionIdeal 1) : F.completedCounit R u = 1 :=
  sub_eq_zero.mp <| by simpa only [map_sub, map_one] using F.completedCounit_eq_zero_of_mem R hu

/-- When `ker ε ≤ F.ideal 1`, `F.completionIdeal 1` is the kernel of `completedCounit`. -/
theorem mem_completionIdeal_one_iff_completedCounit_eq_zero
    (hker : RingHom.ker (Bialgebra.counitAlgHom R A) ≤ F.ideal 1) (x : F.completion) :
    x ∈ F.completionIdeal 1 ↔ F.completedCounit R x = 0 := by
  refine ⟨F.completedCounit_eq_zero_of_mem R, fun hx => ?_⟩
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (F.projection 0 x)
  rw [completionIdeal_succ, RingHom.mem_ker, ← ha, Ideal.Quotient.eq_zero_iff_mem]
  exact hker <| RingHom.mem_ker.mpr <| by
    rw [Bialgebra.counitAlgHom_apply, ← F.completedCounit_of_representative R x a ha, hx]

/-- When `ker ε ≤ F.ideal 1`, `u - 1 ∈ F.completionIdeal 1` iff `ε̂(u) = 1`. -/
theorem sub_one_mem_completionIdeal_one_iff_completedCounit_eq_one
    (hker : RingHom.ker (Bialgebra.counitAlgHom R A) ≤ F.ideal 1) (u : F.completion) :
    u - 1 ∈ F.completionIdeal 1 ↔ F.completedCounit R u = 1 := by
  rw [F.mem_completionIdeal_one_iff_completedCounit_eq_zero R hker (u - 1), map_sub, map_one,
    sub_eq_zero]

/-- A filtered bialgebra homomorphism intertwines `completedCoproduct` along a monotone modulus. -/
theorem completedCoproduct_mapCompletionₐ {B : Type*} [Ring B] [Bialgebra R B]
    (G : AlgFiltration B) [G.IsBialgFiltration R] (f : A →ₐc[R] B) (l : ℕ → ℕ) (hl : Monotone l)
    (hf : ∀ k, F.ideal (l k + 1) ≤ (G.ideal (k + 1)).comap (f : A →ₐ[R] B)) (x : F.completion) :
    G.completedCoproduct R (F.mapCompletionₐ G (f : A →ₐ[R] B) l hl hf x) =
      (F.tensorProduct R F).mapCompletionₐ (G.tensorProduct R G)
        (Algebra.TensorProduct.map (f : A →ₐ[R] B) (f : A →ₐ[R] B)) (fun k => l k + l k)
        (hl.add hl) (F.tensorProduct_ideal_le_comap_map_of_moduli R F G G
          (f : A →ₐ[R] B) (f : A →ₐ[R] B) l l hf hf) (F.completedCoproduct R x) := by
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
  refine AlgHom.congr_fun ?_ x
  dsimp only [completedCoproduct]
  rw [← F.mapCompletionₐ_comp G (f : A →ₐ[R] B) l hl hf (G.tensorProduct R G)
    (Bialgebra.comulAlgHom R B) id monotone_id _,
    ← F.mapCompletionₐ_comp (F.tensorProduct R F) (Bialgebra.comulAlgHom R A) id monotone_id _
    (G.tensorProduct R G) (Algebra.TensorProduct.map (f : A →ₐ[R] B) (f : A →ₐ[R] B))
    (fun k => l k + l k) (hl.add hl) _]
  simpa only [f.map_comp_comulAlgHom] using (F.mapCompletionₐ_eq (G.tensorProduct R G)
    ((Bialgebra.comulAlgHom R B).comp (f : A →ₐ[R] B)) (id ∘ fun k => l k + l k)
    (monotone_id.comp (hl.add hl)) _ (l ∘ id) (hl.comp monotone_id) _).symm

/-- Any filtered bialgebra homomorphism preserves `completedCounit` along any monotone modulus. -/
@[simp] theorem completedCounit_mapCompletionₐ {B : Type*} [Ring B] [Bialgebra R B]
    (G : AlgFiltration B) [G.IsBialgFiltration R] (f : A →ₐc[R] B) (l : ℕ → ℕ) (hl : Monotone l)
    (hf : ∀ k, F.ideal (l k + 1) ≤ (G.ideal (k + 1)).comap (f : A →ₐ[R] B)) (x : F.completion) :
    G.completedCounit R (F.mapCompletionₐ G (f : A →ₐ[R] B) l hl hf x) = F.completedCounit R x := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (F.projection (l 0) x)
  rw [G.completedCounit_of_representative R _ (f a) (by simp [projection_mapCompletionₐ, ← ha]),
    F.completedCounit_of_representative R x a
      (by rw [← F.factor_projection (Nat.zero_le (l 0)) x, ← ha, Ideal.Quotient.factor_mk])]
  exact AlgHom.congr_fun f.counitAlgHom_comp a

/-- An element `x : F.completion` is *completed group-like* if `ε̂(x) = 1` and `Δ̂(x) = x ⊗̂ x`. -/
structure IsCompletedGroupLike (x : F.completion) : Prop where
  /-- A completed group-like element has completed counit `1`. -/
  completedCounit_eq_one : F.completedCounit R x = 1
  /-- A completed group-like element has completed coproduct `x ⊗̂ x`. -/
  completedCoproduct_eq_completedTensor_self : F.completedCoproduct R x = F.completedTensor R F x x

/-- Unfolded characterization of completed group-like elements. -/
theorem isCompletedGroupLike_iff {x : F.completion} :
    F.IsCompletedGroupLike R x ↔
      F.completedCounit R x = 1 ∧ F.completedCoproduct R x = F.completedTensor R F x x :=
  ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩⟩

/-- An element `x` of `F.completion` is *completed primitive* when `Δ̂(x) = x ⊗̂ 1 + 1 ⊗̂ x`. -/
def IsCompletedPrimitive (x : F.completion) : Prop :=
  F.completedCoproduct R x = F.completedTensor R F x 1 + F.completedTensor R F 1 x

/-- Unfolded characterization of completed primitive elements. -/
theorem isCompletedPrimitive_iff {x : F.completion} :
    F.IsCompletedPrimitive R x ↔
      F.completedCoproduct R x = F.completedTensor R F x 1 + F.completedTensor R F 1 x := Iff.rfl

/-- Completed primitivity in terms of the left and right completed tensor inclusions. -/
theorem isCompletedPrimitive_iff_includeCompletion {x : F.completion} :
    F.IsCompletedPrimitive R x ↔ F.completedCoproduct R x =
      F.includeLeftCompletion R F x + F.includeRightCompletion R F x := by
  simp [IsCompletedPrimitive]

section GroupLike

variable {R F}

/-- The identity element `1` is completed group-like. -/
@[simp] theorem IsCompletedGroupLike.one : F.IsCompletedGroupLike R 1 := ⟨map_one _, by simp⟩

/-- Completed group-like elements are closed under multiplication. -/
theorem IsCompletedGroupLike.mul {x y : F.completion}
    (hx : F.IsCompletedGroupLike R x) (hy : F.IsCompletedGroupLike R y) :
    F.IsCompletedGroupLike R (x * y) :=
  ⟨by simp [map_mul, hx.completedCounit_eq_one, hy.completedCounit_eq_one],
   by rw [map_mul, hx.completedCoproduct_eq_completedTensor_self,
     hy.completedCoproduct_eq_completedTensor_self, F.completedTensor_mul R F]⟩

/-- Completed group-like elements are closed under natural powers. -/
theorem IsCompletedGroupLike.pow {x : F.completion} (hx : F.IsCompletedGroupLike R x) :
    ∀ n : ℕ, F.IsCompletedGroupLike R (x ^ n)
  | 0 => by simpa only [pow_zero] using IsCompletedGroupLike.one
  | n + 1 => by simpa only [pow_succ] using (hx.pow n).mul hx

/-- Completed group-like elements are closed under two-sided multiplicative inverses. -/
theorem IsCompletedGroupLike.of_mul_eq_one {x y : F.completion}
    (hxy : x * y = 1) (hyx : y * x = 1) (hx : F.IsCompletedGroupLike R x) :
    F.IsCompletedGroupLike R y :=
  ⟨left_inv_eq_right_inv (a := F.completedCounit R x)
      (by rw [← map_mul, hyx, map_one]) (by rw [hx.completedCounit_eq_one, one_mul]),
   left_inv_eq_right_inv (a := F.completedCoproduct R x) (by rw [← map_mul, hyx, map_one])
      (by rw [hx.completedCoproduct_eq_completedTensor_self, ← F.completedTensor_mul R F, hxy,
        F.completedTensor_one_left R F, map_one])⟩

/-- Multiplicative inversion on `F.completionˣ` preserves completed group-likeness. -/
@[simp] theorem isCompletedGroupLike_unitsInv {u : F.completionˣ} :
    F.IsCompletedGroupLike R (↑u⁻¹ : F.completion) ↔ F.IsCompletedGroupLike R (u : F.completion) :=
  ⟨IsCompletedGroupLike.of_mul_eq_one u.inv_mul u.mul_inv,
    IsCompletedGroupLike.of_mul_eq_one u.mul_inv u.inv_mul⟩

/-- Canonical images of group-like elements of `A` are completed group-like. -/
theorem isCompletedGroupLike_toCompletion {a : A} (ha : IsGroupLikeElem R a) :
    F.IsCompletedGroupLike R (F.toCompletion a) :=
  ⟨by simp [ha.counit_eq_one], by
    rw [completedCoproduct_toCompletion, ha.comul_eq_tmul_self, completedTensor_toCompletion]⟩

/-- If `ker ε ≤ F.ideal 1`, every completed group-like element is `1` mod `F.completionIdeal 1`. -/
theorem IsCompletedGroupLike.sub_one_mem {u : F.completion} (hu : F.IsCompletedGroupLike R u)
    (hker : RingHom.ker (Bialgebra.counitAlgHom R A) ≤ F.ideal 1) : u - 1 ∈ F.completionIdeal 1 :=
  (F.sub_one_mem_completionIdeal_one_iff_completedCounit_eq_one R hker u).mpr
    hu.completedCounit_eq_one

/-- Filtered bialgebra homomorphisms preserve completed group-likeness along a monotone modulus. -/
theorem IsCompletedGroupLike.map {B : Type*} [Ring B] [Bialgebra R B]
    (G : AlgFiltration B) [G.IsBialgFiltration R] (f : A →ₐc[R] B) (l : ℕ → ℕ) (hl : Monotone l)
    (hf : ∀ k, F.ideal (l k + 1) ≤ (G.ideal (k + 1)).comap (f : A →ₐ[R] B))
    {x : F.completion} (hx : F.IsCompletedGroupLike R x) :
    G.IsCompletedGroupLike R (F.mapCompletionₐ G (f : A →ₐ[R] B) l hl hf x) :=
  ⟨by rw [F.completedCounit_mapCompletionₐ R G f l hl hf x, hx.completedCounit_eq_one], by
    rw [F.completedCoproduct_mapCompletionₐ R G f l hl hf x,
      hx.completedCoproduct_eq_completedTensor_self,
      F.mapCompletionₐ_completedTensor_of_moduli R F G G (f : A →ₐ[R] B) (f : A →ₐ[R] B)
        l l hl hl hf hf x x]⟩

end GroupLike

/-- The submonoid of completed group-like elements of `F.completion`. -/
def completedGroupLikeSubmonoid : Submonoid F.completion where
  carrier := {x | F.IsCompletedGroupLike R x}
  one_mem' := IsCompletedGroupLike.one
  mul_mem' hx hy := hx.mul hy

/-- Membership in `F.completedGroupLikeSubmonoid R` unfolds to `F.IsCompletedGroupLike R`. -/
@[simp] theorem mem_completedGroupLikeSubmonoid_iff {x : F.completion} :
    x ∈ F.completedGroupLikeSubmonoid R ↔ F.IsCompletedGroupLike R x := Iff.rfl

/-- The subgroup of `F.completionˣ` consisting of units that are completed group-like. -/
def completedGroupLikeSubgroup : Subgroup F.completionˣ where
  carrier := {u | F.IsCompletedGroupLike R (u : F.completion)}
  one_mem' := IsCompletedGroupLike.one
  mul_mem' hx hy := hx.mul hy
  inv_mem' hx := isCompletedGroupLike_unitsInv.mpr hx

/-- Membership in `F.completedGroupLikeSubgroup R` unfolds to `F.IsCompletedGroupLike R`. -/
@[simp] theorem mem_completedGroupLikeSubgroup_iff {u : F.completionˣ} :
    u ∈ F.completedGroupLikeSubgroup R ↔ F.IsCompletedGroupLike R (u : F.completion) := Iff.rfl

section Primitive

variable {R F}

/-- Every completed primitive element has completed counit zero. -/
theorem IsCompletedPrimitive.completedCounit_eq_zero {x : F.completion}
    (hx : F.IsCompletedPrimitive R x) : F.completedCounit R x = 0 := by
  let ε₂ : A ⊗[R] A →ₐ[R] R := Algebra.TensorProduct.lift
    (Bialgebra.counitAlgHom R A) (Bialgebra.counitAlgHom R A) fun _ _ => Commute.all _ _
  have hker₂ : (F.tensorProduct R F).ideal 1 ≤ RingHom.ker ε₂ := fun t ht => by
    have hsub : tensorFiltrationTail (fun n => (F.ideal n).restrictScalars R)
        (fun n => (F.ideal n).restrictScalars R) 1 ≤ LinearMap.ker ε₂.toLinearMap :=
      (tensorFiltrationTail_le_iff _ _).mpr fun a b hab u hu v hv => by
        rw [LinearMap.mem_ker, AlgHom.toLinearMap_apply]; dsimp [ε₂]
        by_cases ha : 1 ≤ a
        · simp [RingHom.mem_ker.mp (IsBialgFiltration.ideal_one_le_ker_counit (F.antitone ha hu))]
        · simp [RingHom.mem_ker.mp (IsBialgFiltration.ideal_one_le_ker_counit
            (F.antitone (by omega) hv))]
    exact hsub ((F.mem_tensorProduct_ideal_iff R F).mp ht)
  let E : (F.tensorProduct R F).completion →ₐ[R] R :=
    (Ideal.Quotient.liftₐ ((F.tensorProduct R F).ideal 1) ε₂
      fun _ ht => RingHom.mem_ker.mp (hker₂ ht)).comp ((F.tensorProduct R F).projectionₐ (R := R) 0)
  have hε₂_comul (a : A) : ε₂ (Coalgebra.comul (R := R) a) = Coalgebra.counit (R := R) a := by
    have hlin : ε₂.toLinearMap = (Coalgebra.counit (R := R)).comp
        ((TensorProduct.lid R A).toLinearMap.comp (Coalgebra.counit.rTensor A)) :=
      TensorProduct.ext' fun _ _ => by simp [ε₂]
    simpa only [AlgHom.toLinearMap_apply, LinearMap.comp_apply, Coalgebra.rTensor_counit_comul,
      LinearEquiv.coe_coe, TensorProduct.lid_tmul, one_smul] using
      LinearMap.congr_fun hlin (Coalgebra.comul (R := R) a)
  have hE_mk {t z} (hz : (F.tensorProduct R F).projection 0 z = Ideal.Quotient.mk _ t) :
      E z = ε₂ t := by simp only [E, AlgHom.comp_apply, projectionₐ_apply, hz]; rfl
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (F.projection 0 x)
  have hsum := congrArg E hx
  rw [map_add, hE_mk (t := Coalgebra.comul (R := R) a)
      (by simp [projection_completedCoproduct, ← ha]), hε₂_comul a,
    hE_mk (F.projection_completedTensor_of_representatives R F 0 x 1 a 1 ha (by simp)),
    hE_mk (F.projection_completedTensor_of_representatives R F 0 1 x 1 a (by simp) ha)] at hsum
  simp only [ε₂, Algebra.TensorProduct.lift_tmul, map_one, mul_one, one_mul,
    Bialgebra.counitAlgHom_apply, ← F.completedCounit_of_representative R x a ha] at hsum
  simpa using congrArg (· - F.completedCounit R x) hsum.symm

/-- When `ker ε ≤ F.ideal 1`, every completed primitive element belongs to `F.completionIdeal 1`. -/
theorem IsCompletedPrimitive.mem_completionIdeal_one {x : F.completion}
    (hx : F.IsCompletedPrimitive R x)
    (hker : RingHom.ker (Bialgebra.counitAlgHom R A) ≤ F.ideal 1) :
    x ∈ F.completionIdeal 1 :=
  (F.mem_completionIdeal_one_iff_completedCounit_eq_zero R hker x).mpr hx.completedCounit_eq_zero

/-- Zero is completed primitive. -/
@[simp] theorem IsCompletedPrimitive.zero : F.IsCompletedPrimitive R 0 := by
  simp [isCompletedPrimitive_iff_includeCompletion]

/-- Completed primitive elements are closed under addition. -/
theorem IsCompletedPrimitive.add {x y : F.completion}
    (hx : F.IsCompletedPrimitive R x) (hy : F.IsCompletedPrimitive R y) :
    F.IsCompletedPrimitive R (x + y) := by
  rw [isCompletedPrimitive_iff_includeCompletion] at hx hy ⊢
  rw [map_add, hx, hy, map_add, map_add]; abel

/-- Completed primitive elements are closed under negation. -/
theorem IsCompletedPrimitive.neg {x : F.completion} (hx : F.IsCompletedPrimitive R x) :
    F.IsCompletedPrimitive R (-x) := by
  rw [isCompletedPrimitive_iff_includeCompletion] at hx ⊢; rw [map_neg, hx, map_neg, map_neg]; abel

/-- Negation preserves completed primitivity as an equivalence. -/
@[simp] theorem isCompletedPrimitive_neg {x : F.completion} :
    F.IsCompletedPrimitive R (-x) ↔ F.IsCompletedPrimitive R x :=
  ⟨fun h => neg_neg x ▸ h.neg, IsCompletedPrimitive.neg⟩

/-- Completed primitive elements are closed under subtraction. -/
theorem IsCompletedPrimitive.sub {x y : F.completion}
    (hx : F.IsCompletedPrimitive R x) (hy : F.IsCompletedPrimitive R y) :
    F.IsCompletedPrimitive R (x - y) := by simpa only [sub_eq_add_neg] using hx.add hy.neg

/-- Completed primitive elements are closed under scalar multiplication. -/
theorem IsCompletedPrimitive.smul (r : R) {x : F.completion} (hx : F.IsCompletedPrimitive R x) :
    F.IsCompletedPrimitive R (r • x) := by
  rw [isCompletedPrimitive_iff_includeCompletion] at hx ⊢; simp [hx, smul_add]

/-- Completed primitive elements are closed under associative commutators `x * y - y * x`. -/
theorem IsCompletedPrimitive.commutator {x y : F.completion}
    (hx : F.IsCompletedPrimitive R x) (hy : F.IsCompletedPrimitive R y) :
    F.IsCompletedPrimitive R (x * y - y * x) := by
  rw [isCompletedPrimitive_iff_includeCompletion] at hx hy ⊢
  simp only [map_sub, map_mul, hx, hy, add_mul, mul_add,
    (F.commute_includeLeftCompletion_includeRightCompletion R F x y).eq,
    (F.commute_includeLeftCompletion_includeRightCompletion R F y x).eq]; abel

/-- For any order-`k` representative `u` of a completed primitive `x`, `Δ(u) - (u ⊗ 1 + 1 ⊗ u)`
lies in `(F.tensorProduct R F).ideal (k + 1)`. -/
theorem IsCompletedPrimitive.comul_sub_mem_tensorProduct_ideal {x : F.completion}
    (hx : F.IsCompletedPrimitive R x) {k : ℕ} {u : A}
    (hu : Ideal.Quotient.mk (F.ideal (k + 1)) u = F.projection k x) :
    Coalgebra.comul (R := R) u - (u ⊗ₜ[R] 1 + 1 ⊗ₜ[R] u) ∈ (F.tensorProduct R F).ideal (k + 1) := by
  have hk := congrArg ((F.tensorProduct R F).projection k)
    ((F.isCompletedPrimitive_iff_includeCompletion R).mp hx)
  rw [projection_completedCoproduct, map_add, projection_includeLeftCompletion,
    projection_includeRightCompletion, ← hu] at hk
  simp only [Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk, Bialgebra.comulAlgHom_apply,
    Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
    ← map_add] at hk
  exact Ideal.Quotient.eq.mp hk

/-- Canonical images of primitive elements of `A` are completed primitive. -/
theorem isCompletedPrimitive_toCompletion {a : A} (ha : Bialgebra.IsPrimitiveElem R a) :
    F.IsCompletedPrimitive R (F.toCompletion a) := by
  rw [isCompletedPrimitive_iff_includeCompletion, completedCoproduct_toCompletion,
    ha.comul_eq_tmul_add_tmul, map_add, includeLeftCompletion_toCompletion,
    includeRightCompletion_toCompletion, add_comm]

/-- A filtered bialgebra homomorphism preserves completed primitivity along a monotone modulus. -/
theorem IsCompletedPrimitive.map {B : Type*} [Ring B] [Bialgebra R B]
    (G : AlgFiltration B) [G.IsBialgFiltration R] (f : A →ₐc[R] B) (l : ℕ → ℕ) (hl : Monotone l)
    (hf : ∀ k, F.ideal (l k + 1) ≤ (G.ideal (k + 1)).comap (f : A →ₐ[R] B))
    {x : F.completion} (hx : F.IsCompletedPrimitive R x) :
    G.IsCompletedPrimitive R (F.mapCompletionₐ G (f : A →ₐ[R] B) l hl hf x) := by
  let f' : A →ₐ[R] B := f
  rw [isCompletedPrimitive_iff, F.completedCoproduct_mapCompletionₐ R G f l hl hf x, hx, map_add,
    F.mapCompletionₐ_completedTensor_of_moduli R F G G f' f' l l hl hl hf hf x 1,
    F.mapCompletionₐ_completedTensor_of_moduli R F G G f' f' l l hl hl hf hf 1 x, map_one]

end Primitive

/-- The `R`-submodule of completed primitive elements of `F.completion`. -/
def completedPrimitiveSubmodule : Submodule R F.completion where
  carrier := {x | F.IsCompletedPrimitive R x}
  zero_mem' := IsCompletedPrimitive.zero
  add_mem' hx hy := hx.add hy
  smul_mem' r _ hx := hx.smul r

/-- Membership in `F.completedPrimitiveSubmodule R` unfolds to `F.IsCompletedPrimitive R`. -/
@[simp] theorem mem_completedPrimitiveSubmodule_iff {x : F.completion} :
    x ∈ F.completedPrimitiveSubmodule R ↔ F.IsCompletedPrimitive R x := Iff.rfl

section Exp

variable [Algebra ℚ A]

/-- In a rational filtered bialgebra, `F.completedExp x` is completed group-like iff `x` is
completed primitive. -/
@[simp] theorem isCompletedGroupLike_completedExp_iff (x : F.completionIdeal 1) :
    F.IsCompletedGroupLike R (F.completedExp x) ↔ F.IsCompletedPrimitive R (x : F.completion) := by
  have : SMulCommClass R ℚ A :=
    ⟨fun r _ _ => by simp only [Algebra.smul_def, ← mul_assoc, Algebra.commutes r]⟩
  let T := F.tensorProduct R F
  have hcoprod := F.map_completedExp_of_projection T id (F.completedCoproduct R)
    (fun k => (Ideal.quotientMapₐ (T.ideal (k + 1)) (Bialgebra.comulAlgHom R A)
      (IsBialgFiltration.ideal_le_comap_comul (R := R) (F := F) (k + 1))).toRingHom)
    (F.projection_completedCoproduct R) x (F.completedCoproduct_mem_completionIdeal R x.property)
  let xl : T.completionIdeal 1 :=
    ⟨F.includeLeftCompletion R F x, F.includeLeftCompletion_mem_completionIdeal R F x.property⟩
  let xr : T.completionIdeal 1 :=
    ⟨F.includeRightCompletion R F x, F.includeRightCompletion_mem_completionIdeal R F x.property⟩
  have hleft := F.map_completedExp_of_projection T id (F.includeLeftCompletion R F)
    (fun k => (Ideal.quotientMapₐ (T.ideal (k + 1))
      (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A)
      (F.ideal_le_comap_includeLeft R F (k + 1))).toRingHom)
    (F.projection_includeLeftCompletion R F) x xl.property
  have hright := F.map_completedExp_of_projection T id (F.includeRightCompletion R F)
    (fun k => (Ideal.quotientMapₐ (T.ideal (k + 1))
      (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A)
      (F.ideal_le_comap_includeRight R F (k + 1))).toRingHom)
    (F.projection_includeRightCompletion R F) x xr.property
  have htensor : F.completedTensor R F (F.completedExp x) (F.completedExp x) =
      T.completedExp (xl + xr) := by
    rw [completedTensor_apply, hleft, hright, ← T.completedExp_add xl xr
      (F.commute_includeLeftCompletion_includeRightCompletion R F x x)]
  rw [isCompletedGroupLike_iff,
    and_iff_right (F.completedCounit_eq_one_of_sub_one_mem R (F.completedExp_sub_one_mem x)),
    hcoprod, htensor, isCompletedPrimitive_iff_includeCompletion]
  exact ⟨fun h => congrArg Subtype.val <| T.completedExpEquiv.injective <|
    Subtype.ext <| by simpa only [T.coe_completedExpEquiv] using h,
    fun h => congrArg T.completedExp (Subtype.ext h)⟩

/-- In a rational filtered bialgebra, `F.completedLog u` is completed primitive iff `u` is
completed group-like. -/
@[simp] theorem isCompletedPrimitive_completedLog_iff
    (u : {u : F.completion // u - 1 ∈ F.completionIdeal 1}) :
    F.IsCompletedPrimitive R (F.completedLog u) ↔ F.IsCompletedGroupLike R (u : F.completion) := by
  rw [← F.isCompletedGroupLike_completedExp_iff R ⟨F.completedLog u, F.completedLog_mem u⟩,
    F.completedExp_completedLog]

/-- Exponential coordinates identify completed primitives in `F.completionIdeal 1` with completed
group-like elements congruent to `1` modulo `F.completionIdeal 1`. -/
noncomputable def completedPrimitiveCompletionIdealEquivGroupLike :
    {x : F.completionIdeal 1 // F.IsCompletedPrimitive R (x : F.completion)} ≃
      {u : F.completion // u - 1 ∈ F.completionIdeal 1 ∧ F.IsCompletedGroupLike R u} :=
  (F.completedExpEquiv.subtypeEquiv fun x => by
    rw [F.coe_completedExpEquiv]; exact (F.isCompletedGroupLike_completedExp_iff R x).symm).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun u : F.completion => u - 1 ∈ F.completionIdeal 1) (F.IsCompletedGroupLike R))

/-- The forward map of `F.completedPrimitiveCompletionIdealEquivGroupLike R` is `F.completedExp`. -/
@[simp] theorem coe_completedPrimitiveCompletionIdealEquivGroupLike
    (x : {x : F.completionIdeal 1 // F.IsCompletedPrimitive R (x : F.completion)}) :
    (F.completedPrimitiveCompletionIdealEquivGroupLike R x : F.completion) =
      F.completedExp x.val :=
  F.coe_completedExpEquiv x.val

/-- The inverse map of `F.completedPrimitiveCompletionIdealEquivGroupLike R` is `F.completedLog`. -/
@[simp] theorem coe_completedPrimitiveCompletionIdealEquivGroupLike_symm
    (u : {u : F.completion // u - 1 ∈ F.completionIdeal 1 ∧ F.IsCompletedGroupLike R u}) :
    ((F.completedPrimitiveCompletionIdealEquivGroupLike R).symm u : F.completion) =
      F.completedLog ⟨u.val, u.property.1⟩ := F.coe_completedExpEquiv_symm ⟨u.val, u.property.1⟩

/-- When `ker ε ≤ F.ideal 1`, exponential coordinates identify all completed primitive elements
with all completed group-like elements. -/
noncomputable def completedPrimitiveEquivGroupLike
    (hker : RingHom.ker (Bialgebra.counitAlgHom R A) ≤ F.ideal 1) :
    {x : F.completion // F.IsCompletedPrimitive R x} ≃
      {u : F.completion // F.IsCompletedGroupLike R u} :=
  (Equiv.subtypeSubtypeEquivSubtype (fun {_} hx => hx.mem_completionIdeal_one hker)).symm.trans <|
    (F.completedPrimitiveCompletionIdealEquivGroupLike R).trans <|
      Equiv.subtypeEquivRight fun _ => and_iff_right_of_imp (fun hu => hu.sub_one_mem hker)

/-- The forward map of `F.completedPrimitiveEquivGroupLike R hker` is `F.completedExp`. -/
@[simp] theorem coe_completedPrimitiveEquivGroupLike
    (hker : RingHom.ker (Bialgebra.counitAlgHom R A) ≤ F.ideal 1)
    (x : {x : F.completion // F.IsCompletedPrimitive R x}) :
    (F.completedPrimitiveEquivGroupLike R hker x : F.completion) =
      F.completedExp ⟨x.val, x.property.mem_completionIdeal_one hker⟩ :=
  F.coe_completedExpEquiv ⟨x.val, x.property.mem_completionIdeal_one hker⟩

/-- The inverse map of `F.completedPrimitiveEquivGroupLike R hker` is `F.completedLog`. -/
@[simp] theorem coe_completedPrimitiveEquivGroupLike_symm
    (hker : RingHom.ker (Bialgebra.counitAlgHom R A) ≤ F.ideal 1)
    (u : {u : F.completion // F.IsCompletedGroupLike R u}) :
    ((F.completedPrimitiveEquivGroupLike R hker).symm u : F.completion) =
      F.completedLog ⟨u.val, u.property.sub_one_mem hker⟩ :=
  F.coe_completedExpEquiv_symm ⟨u.val, u.property.sub_one_mem hker⟩

end Exp

end Completion

end TauCeti.AlgFiltration
