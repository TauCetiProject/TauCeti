/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Topology.ContinuousMap.Algebra
public import TauCeti.Algebra.DirectSum.Ring
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Product.Basic
import Mathlib.Data.List.OfFn
import TauCeti.Topology.ContinuousMap.Pi

/-!
# The cup product on continuous inhomogeneous cochains

For a topological monoid `G` acting continuously by ring endomorphisms on `R`, the cup
product of continuous cochains of degrees `p` and `q` is given on concatenated tuples by

`(f ∪ g)(x ++ y) = f(x) * ((x₁ ⋯ xₚ) • g(y))`.

The translating element is the ordered product of the first block. Concatenation multiplies
these elements in the same order, giving associativity already on cochains. The constant
one in degree zero is the unit. The resulting `DirectSum.GRing` equips the direct sum of
the groups of continuous cochains with its cup product ring structure, via
`TauCeti.DirectSum.gRingOfMul`. In bidegree `(1,1)`, `ContinuousMap.H2pi_inhomogeneousCup`
identifies the class of the product with `TauCeti.ContCohomology.explicitCup11`.

The translated cup formula is the inhomogeneous version of the Alexander–Whitney product.
See Neukirch, Schmidt and Wingberg, *Cohomology of Number Fields*, Ch. I §4, and
Y. Harpaz and O. Wittenberg, *The Massey vanishing conjecture for number fields*,
Remark 7.1, for its use with nontrivial coefficient actions.
-/

public section

namespace ContinuousMap

variable {G R : Type*} [TopologicalSpace G] [Monoid G] [ContinuousMul G]
  [TopologicalSpace R] {p q r : ℕ}

section Product

variable [Mul R] [ContinuousMul R] [SMul G R] [ContinuousSMul G R]

/-- The inhomogeneous cup product of continuous cochains. The ordered product of the
arguments of the left cochain acts on the value of the right cochain. -/
def inhomogeneousCup (f : C(Fin p → G, R)) (g : C(Fin q → G, R)) : C(Fin (p + q) → G, R) where
  toFun x := f (x ∘ Fin.castAdd q) * ((List.ofFn (x ∘ Fin.castAdd q)).prod • g (x ∘ Fin.natAdd p))
  continuous_toFun := by
    apply (f.continuous.comp (Pi.continuous_precomp' _)).mul
    apply Continuous.smul _ (g.continuous.comp (Pi.continuous_precomp' _))
    simp_rw [List.ofFn_eq_map]
    exact continuous_list_prod _ fun i _ ↦ continuous_apply _

/-- Evaluation on a tuple splits its arguments after the first block. -/
-- The simp normal forms evaluate concatenated tuples and explicit pairs without expanding casts.
theorem inhomogeneousCup_apply (f : C(Fin p → G, R)) (g : C(Fin q → G, R))
    (x : Fin (p + q) → G) :
    f.inhomogeneousCup g x =
      f (x ∘ Fin.castAdd q) * ((List.ofFn (x ∘ Fin.castAdd q)).prod • g (x ∘ Fin.natAdd p)) :=
  (rfl)

/-- Evaluation on concatenated tuples separates the two cochains. -/
@[simp]
theorem inhomogeneousCup_append (f : C(Fin p → G, R)) (g : C(Fin q → G, R))
    (x : Fin p → G) (y : Fin q → G) :
    f.inhomogeneousCup g (Fin.append x y) = f x * ((List.ofFn x).prod • g y) := by
  simp [inhomogeneousCup_apply, Function.comp_def]

/-- In bidegree `(1,1)` the first argument acts on the second cochain value. -/
@[simp]
theorem inhomogeneousCup_one_one_apply (f g : C(Fin 1 → G, R)) (a b : G) :
    f.inhomogeneousCup g ![a, b] = f ![a] * (a • g ![b]) := by
  have ht : Fin.append ![a] ![b] = ![a, b] := by
    funext i
    fin_cases i <;> rfl
  rw [← ht, inhomogeneousCup_append]
  simp [List.ofFn_succ]

end Product

section Zero

variable [MulZeroClass R] [ContinuousMul R]

@[simp]
theorem zero_inhomogeneousCup [SMul G R] [ContinuousSMul G R] (g : C(Fin q → G, R)) :
    (0 : C(Fin p → G, R)).inhomogeneousCup g = 0 := by
  ext x
  simp [inhomogeneousCup_apply]

@[simp]
theorem inhomogeneousCup_zero [SMulZeroClass G R] [ContinuousSMul G R] (f : C(Fin p → G, R)) :
    f.inhomogeneousCup (0 : C(Fin q → G, R)) = 0 := by
  ext x
  simp [inhomogeneousCup_apply]

end Zero

section Add

variable [NonUnitalNonAssocSemiring R] [ContinuousAdd R] [ContinuousMul R]

@[simp]
theorem add_inhomogeneousCup [SMul G R] [ContinuousSMul G R]
    (f₁ f₂ : C(Fin p → G, R)) (g : C(Fin q → G, R)) :
    (f₁ + f₂).inhomogeneousCup g = f₁.inhomogeneousCup g + f₂.inhomogeneousCup g := by
  ext x
  simp [inhomogeneousCup_apply, add_mul]

@[simp]
theorem inhomogeneousCup_add [DistribSMul G R] [ContinuousSMul G R]
    (f : C(Fin p → G, R)) (g₁ g₂ : C(Fin q → G, R)) :
    f.inhomogeneousCup (g₁ + g₂) = f.inhomogeneousCup g₁ + f.inhomogeneousCup g₂ := by
  ext x
  simp [inhomogeneousCup_apply, smul_add, mul_add]

end Add

section NegSub

variable [NonUnitalNonAssocRing R] [IsTopologicalAddGroup R] [ContinuousMul R]

@[simp]
theorem neg_inhomogeneousCup [SMul G R] [ContinuousSMul G R]
    (f : C(Fin p → G, R)) (g : C(Fin q → G, R)) :
    (-f).inhomogeneousCup g = -(f.inhomogeneousCup g) := by
  ext x
  simp [inhomogeneousCup_apply]

@[simp]
theorem inhomogeneousCup_neg [DistribSMul G R] [ContinuousSMul G R]
    (f : C(Fin p → G, R)) (g : C(Fin q → G, R)) :
    f.inhomogeneousCup (-g) = -(f.inhomogeneousCup g) := by
  ext x
  simp [inhomogeneousCup_apply]

@[simp]
theorem sub_inhomogeneousCup [SMul G R] [ContinuousSMul G R]
    (f₁ f₂ : C(Fin p → G, R)) (g : C(Fin q → G, R)) :
    (f₁ - f₂).inhomogeneousCup g = f₁.inhomogeneousCup g - f₂.inhomogeneousCup g := by
  simp only [sub_eq_add_neg, add_inhomogeneousCup, neg_inhomogeneousCup]

@[simp]
theorem inhomogeneousCup_sub [DistribSMul G R] [ContinuousSMul G R]
    (f : C(Fin p → G, R)) (g₁ g₂ : C(Fin q → G, R)) :
    f.inhomogeneousCup (g₁ - g₂) = f.inhomogeneousCup g₁ - f.inhomogeneousCup g₂ := by
  simp only [sub_eq_add_neg, inhomogeneousCup_add, inhomogeneousCup_neg]

end NegSub

section Scalar

variable {k : Type*} [Mul R] [ContinuousMul R] [SMul G R] [ContinuousSMul G R]
  [SMul k R] [ContinuousConstSMul k R]

-- Rewrite scalar cups before simp turns integer scalar multiplication into ring multiplication.
@[simp↓]
theorem smul_inhomogeneousCup [IsScalarTower k R R]
    (f : C(Fin p → G, R)) (g : C(Fin q → G, R)) (c : k) :
    (c • f).inhomogeneousCup g = c • f.inhomogeneousCup g := by
  ext x
  simp [inhomogeneousCup_apply, smul_mul_assoc]

@[simp↓]
theorem inhomogeneousCup_smul [SMulCommClass G k R] [SMulCommClass k R R]
    (f : C(Fin p → G, R)) (g : C(Fin q → G, R)) (c : k) :
    f.inhomogeneousCup (c • g) = c • f.inhomogeneousCup g := by
  ext x
  simp [inhomogeneousCup_apply, smul_comm _ c, mul_smul_comm]

end Scalar

section LeftUnit

variable [MulOneClass R] [ContinuousMul R] [MulAction G R] [ContinuousSMul G R]

/-- The degree-zero unit on the left, with the canonical reindexing of the arguments. -/
@[simp]
theorem one_inhomogeneousCup (f : C(Fin p → G, R)) :
    (1 : C(Fin 0 → G, R)).inhomogeneousCup f = f.comp (precomp (Fin.natAdd 0)) := by
  ext x
  simp [inhomogeneousCup_apply, precomp, Function.comp_def]

end LeftUnit

section Monoid

variable [Monoid R] [ContinuousMul R] [MulDistribMulAction G R] [ContinuousSMul G R]

/-- The degree-zero unit on the right. -/
@[simp]
theorem inhomogeneousCup_one (f : C(Fin p → G, R)) :
    f.inhomogeneousCup (1 : C(Fin 0 → G, R)) = f := by
  ext x
  rw [inhomogeneousCup_apply f (1 : C(Fin 0 → G, R)) x]
  simp [Function.comp_def]

/-- Associativity on cochains, under the canonical identification of the two total degrees. -/
theorem inhomogeneousCup_assoc (f : C(Fin p → G, R)) (g : C(Fin q → G, R))
    (h : C(Fin r → G, R)) :
    (f.inhomogeneousCup g).inhomogeneousCup h =
      (f.inhomogeneousCup (g.inhomogeneousCup h)).comp
        (precomp (Fin.cast (Nat.add_assoc p q r).symm)) := by
  ext t
  obtain ⟨xy, z, rfl⟩ : ∃ xy z, Fin.append xy z = t :=
    ⟨_, _, Fin.append_castAdd_natAdd⟩
  obtain ⟨x, y, rfl⟩ : ∃ x y, Fin.append x y = xy :=
    ⟨_, _, Fin.append_castAdd_natAdd⟩
  have ha : (fun j ↦ Fin.append (Fin.append x y) z (Fin.cast (Nat.add_assoc p q r).symm j)) =
      Fin.append x (Fin.append y z) := by
    funext j
    simp [Fin.append_assoc]
  simp [comp_apply, precomp, ha, List.ofFn_fin_append, mul_smul, smul_mul', mul_assoc]

end Monoid

section Naturality

variable {H S : Type*} [TopologicalSpace H] [Monoid H] [ContinuousMul H]
  [Mul R] [ContinuousMul R] [SMul G R] [ContinuousSMul G R]
  [TopologicalSpace S] [Mul S] [ContinuousMul S] [SMul H S] [ContinuousSMul H S]
  {F E : Type*} [FunLike F H G] [MonoidHomClass F H G] [ContinuousMapClass F H G]
  [FunLike E R S] [MulHomClass E R S] [ContinuousMapClass E R S]

/-- Pullback in the monoid and an equivariant change of coefficients preserve cup products. -/
theorem comp_inhomogeneousCup_piMap (f : C(Fin p → G, R)) (g : C(Fin q → G, R))
    (φ : F) (ψ : E)
    (hψ : ∀ (a : H) (b : R), ψ (φ a • b) = a • ψ b) :
    (ψ : C(R, S)).comp ((f.inhomogeneousCup g).comp (piMap fun _ ↦ (φ : C(H, G)))) =
      ((ψ : C(R, S)).comp (f.comp (piMap fun _ ↦ (φ : C(H, G))))).inhomogeneousCup
        ((ψ : C(R, S)).comp (g.comp (piMap fun _ ↦ (φ : C(H, G))))) := by
  have pullback {n : ℕ} (x : Fin n → H) :
      piMap (fun _ ↦ (φ : C(H, G))) x = fun i ↦ φ (x i) := by
    funext i
    simp only [piMap_apply, ContinuousMap.coe_ofClass]
  ext t
  simp only [comp_apply, pullback, inhomogeneousCup_apply, Function.comp_def,
    ContinuousMap.coe_ofClass, map_mul]
  rw [List.ofFn_comp' _ φ, ← map_list_prod, hψ]

end Naturality

end ContinuousMap

namespace TauCeti.ContCohomology

open ContinuousMap

variable {G R : Type*} [TopologicalSpace G] [Monoid G] [ContinuousMul G] [TopologicalSpace R]

section Bilinear

variable (k : Type*) [CommSemiring k] [Semiring R] [ContinuousAdd R] [ContinuousMul R]
  [Algebra k R] [ContinuousConstSMul k R] [DistribSMul G R] [ContinuousSMul G R]
  [SMulCommClass G k R]

/-- The cup is bilinear over scalars commuting with the action on the coefficients. -/
def inhomogeneousCupLinearMap (p q : ℕ) :
    C(Fin p → G, R) →ₗ[k] C(Fin q → G, R) →ₗ[k] C(Fin (p + q) → G, R) :=
  LinearMap.mk₂ k inhomogeneousCup
    add_inhomogeneousCup (fun c f g ↦ smul_inhomogeneousCup f g c)
    inhomogeneousCup_add (fun c f g ↦ inhomogeneousCup_smul f g c)

@[simp]
theorem inhomogeneousCupLinearMap_apply {p q : ℕ} (f : C(Fin p → G, R)) (g : C(Fin q → G, R)) :
    inhomogeneousCupLinearMap k p q f g = f.inhomogeneousCup g :=
  LinearMap.mk₂_apply _ _ f g

end Bilinear

section Ring

variable (G R) [Ring R] [IsTopologicalRing R] [MulSemiringAction G R] [ContinuousSMul G R]

-- This form rewrites the product before simplifying the index of the dependent pair.
@[local simp]
private theorem inhomogeneousCupLinearMap_toAddMonoidHom_apply {p q : ℕ}
    (f : C(Fin p → G, R)) (g : C(Fin q → G, R)) :
    (LinearMap.toAddMonoidHom'.comp (inhomogeneousCupLinearMap ℤ p q).toAddMonoidHom) f g =
      f.inhomogeneousCup g := by
  simp

/-- The graded ring of continuous inhomogeneous cochains, with the translated cup as
multiplication and the constant one in degree zero as unit. -/
@[expose, instance_reducible]
def inhomogeneousCochainGRing : DirectSum.GRing (fun n : ℕ ↦ C(Fin n → G, R)) :=
  TauCeti.DirectSum.gRingOfMul
    (fun p q ↦ LinearMap.toAddMonoidHom'.comp (inhomogeneousCupLinearMap ℤ p q).toAddMonoidHom)
    (1 : C(Fin 0 → G, R))
    (fun {i} f ↦ by
      simp only [GradedMonoid.mk, inhomogeneousCupLinearMap_toAddMonoidHom_apply,
        one_inhomogeneousCup]
      apply Sigma.ext (Nat.zero_add i)
      simpa only [Fin.natAdd_zero] using f.comp_precomp_fin_cast_heq (Nat.zero_add i))
    (fun {i} f ↦ by
      simp only [GradedMonoid.mk, inhomogeneousCupLinearMap_toAddMonoidHom_apply]
      exact Sigma.ext (Nat.add_zero i) (inhomogeneousCup_one f).heq)
    (fun {i j k} f g h ↦ by
      simp only [GradedMonoid.mk, inhomogeneousCupLinearMap_toAddMonoidHom_apply]
      rw [inhomogeneousCup_assoc]
      exact Sigma.ext (Nat.add_assoc i j k) (comp_precomp_fin_cast_heq _ (Nat.add_assoc i j k)))

variable {G R}

/-- Multiplication of homogeneous elements is the cup on cochains. -/
@[simp]
theorem inhomogeneousCochainGRing_mul {p q : ℕ} (f : C(Fin p → G, R)) (g : C(Fin q → G, R)) :
    (inhomogeneousCochainGRing G R).mul f g = f.inhomogeneousCup g := by
  simp only [TauCeti.DirectSum.gRingOfMul_gMul, inhomogeneousCupLinearMap_toAddMonoidHom_apply]

/-- The homogeneous unit is the degree-zero constant one. -/
@[simp]
theorem inhomogeneousCochainGRing_one :
    (inhomogeneousCochainGRing G R).one = (1 : C(Fin 0 → G, R)) := by
  simp only [TauCeti.DirectSum.gRingOfMul_gOne]

end Ring

end TauCeti.ContCohomology

namespace ContinuousMap

open TauCeti.ContCohomology

variable {G R : Type*} [Monoid G] [TopologicalSpace G] [ContinuousMul G]
  [Ring R] [TopologicalSpace R] [IsTopologicalRing R] [MulSemiringAction G R] [ContinuousSMul G R]
  (f g : C(Fin 1 → G, R))
  (hf : (fun a ↦ f ![a]) ∈ Z1 G R) (hg : (fun b ↦ g ![b]) ∈ Z1 G R)

include hf hg in
/-- In bidegree `(1,1)` the cup of continuous cocycles is an explicit continuous two-cocycle. -/
theorem inhomogeneousCup_mem_Z2 :
    (fun x : G × G ↦ f.inhomogeneousCup g ![x.1, x.2]) ∈ Z2 G R := by
  simpa only [inhomogeneousCup_one_one_apply, AddMonoidHom.mul_apply] using
    cup11_mem_Z2 G R R R AddMonoidHom.mul continuous_mul
      (fun a b c ↦ (smul_mul' a b c).symm) hf hg

/-- The class of the inhomogeneous cup of one-cocycles is their explicit cohomology cup. -/
theorem H2pi_inhomogeneousCup :
    H2pi G R ⟨_, f.inhomogeneousCup_mem_Z2 g hf hg⟩ =
      explicitCup11 G R R R AddMonoidHom.mul continuous_mul (fun a b c ↦ (smul_mul' a b c).symm)
        (H1pi G R ⟨_, hf⟩) (H1pi G R ⟨_, hg⟩) := by
  refine Eq.trans ?_ (explicitCup11_mk G R R R AddMonoidHom.mul continuous_mul
    (fun a b c ↦ (smul_mul' a b c).symm) ⟨_, hf⟩ ⟨_, hg⟩).symm
  apply congrArg (H2pi G R)
  exact Subtype.ext (funext fun x ↦ inhomogeneousCup_one_one_apply f g x.1 x.2)

end ContinuousMap
