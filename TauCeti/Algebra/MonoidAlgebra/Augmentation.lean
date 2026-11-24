/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.RingTheory.Ideal.Maps
public import TauCeti.Algebra.MonoidAlgebra.RightInvariant
public import TauCeti.Algebra.MonoidAlgebra.SubgroupCharSum

/-!
# The augmentation of a monoid algebra

The coefficient-sum augmentation `R[K] → R` sends each singleton `single k r` to `r`. It is
natural in the monoid `K` and is defined over any semiring `R`. As an `R`-linear map it is
surjective, and its kernel is the augmentation ideal with scalars restricted to `R`.

The augmentation gives the trivial action of `K` on `R` and is the counit of the monoid-algebra
bialgebra. Descriptions of its kernel by generators and the resulting exactness statements live
in `TauCeti.Algebra.MonoidAlgebra.Exactness`.

## Main declarations

* `MonoidAlgebra.augmentation`: the coefficient-sum ring homomorphism.
* `MonoidAlgebra.augmentation_comp_mapDomainRingHom`: naturality in the monoid.
* `MonoidAlgebra.augmentation_mapDomainRingEquiv`: invariance under monoid isomorphisms.
* `MonoidAlgebra.augmentation_mapRingHom`: naturality in the coefficients.
* `MonoidAlgebra.augmentationLinearMap`: the coefficient-sum linear map.
* `MonoidAlgebra.augmentation_smul`: the augmentation is `R`-linear.
* `MonoidAlgebra.augmentationLinearMap_surjective`: surjectivity over any semiring.
* `MonoidAlgebra.ker_augmentationLinearMap`: the linear kernel is the augmentation ideal.
* `MonoidAlgebra.eq_sum_single_of_mul_single_eq_self`: over a semiring in which multiplication by
  `|G|` is injective, an element invariant under every right translation and with augmentation
  `|G| • c` is the constant combination `∑ g, single g c`; for `c = 1` this is the norm.
* `MonoidAlgebra.lift_one_apply`: lifting the trivial character is the augmentation followed by
  `algebraMap`.
* `TauCeti.augmentation_subgroupCharSum`: the augmentation of the character sum
  `∑_{h ∈ H} χ(h) h` is `∑_{h ∈ H} χ(h)`, so that of the norm element of `H` is its order.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.9(b), for the augmentation of a group algebra.
-/

public section

universe u v w

namespace MonoidAlgebra

variable (R : Type u) [Semiring R]

/-- The coefficient-sum augmentation of a monoid algebra. It sends every standard basis element
to `1` and acts identically on coefficients. -/
noncomputable def augmentation (K : Type v) [Monoid K] : MonoidAlgebra R K →+* R :=
  liftNCRingHom (.id R) 1 fun _ _ ↦ Commute.one_right _

/-- The coefficient-sum augmentation sends a singleton to its coefficient. -/
@[simp]
theorem augmentation_single {K : Type v} [Monoid K] (k : K) (r : R) :
    augmentation R K (single k r) = r := by
  simp [augmentation]

/-- The coefficient-sum augmentation is natural with respect to homomorphisms of monoids. -/
@[simp]
theorem augmentation_comp_mapDomainRingHom {M : Type v} {N : Type w} [Monoid M] [Monoid N]
    (f : M →* N) :
    (augmentation R N).comp (mapDomainRingHom R f) = augmentation R M := by
  apply ringHom_ext <;> intro <;> simp

/-- The coefficient-sum augmentation is invariant under an isomorphism of monoids. -/
@[simp]
theorem augmentation_mapDomainRingEquiv {M : Type v} {N : Type w} [Monoid M] [Monoid N]
    (e : M ≃* N) (x : MonoidAlgebra R M) :
    augmentation R N (mapDomainRingEquiv R e x) = augmentation R M x :=
  RingHom.congr_fun (augmentation_comp_mapDomainRingHom R (e : M →* N)) x

/-- The coefficient-sum augmentation is natural with respect to homomorphisms of the
coefficient semirings. -/
@[simp]
theorem augmentation_mapRingHom {S : Type w} [Semiring S] {K : Type v} [Monoid K] (f : R →+* S)
    (x : MonoidAlgebra R K) :
    augmentation S K (mapRingHom K f x) = f (augmentation R K x) := by
  induction x using induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single k r => simp

variable (K : Type v) [Monoid K]

/-- The coefficient-sum augmentation as an `R`-linear map `R[K] → R`. -/
noncomputable def augmentationLinearMap :
    MonoidAlgebra R K →ₗ[R] R where
  toFun := augmentation R K
  map_add' := map_add _
  map_smul' r x := by
    induction x using induction_linear with
    | zero => simp
    | add x y hx hy => simp only [smul_add, map_add, hx, hy, RingHom.id_apply]
    | single k c => simp

@[simp]
theorem augmentationLinearMap_apply (x : MonoidAlgebra R K) :
    augmentationLinearMap R K x = augmentation R K x :=
  (rfl)

/-- The coefficient-sum augmentation is `R`-linear. -/
@[simp]
theorem augmentation_smul (r : R) (x : MonoidAlgebra R K) :
    augmentation R K (r • x) = r * augmentation R K x :=
  (augmentationLinearMap R K).map_smul r x

/-- Over any semiring, the coefficient-sum linear map is surjective. -/
theorem augmentationLinearMap_surjective :
    Function.Surjective (augmentationLinearMap R K) :=
  fun r ↦ ⟨single 1 r, by simp⟩

/-- The kernel of the linear augmentation is the augmentation ideal, with scalars restricted. -/
theorem ker_augmentationLinearMap :
    LinearMap.ker (augmentationLinearMap R K) =
      (RingHom.ker (augmentation R K)).restrictScalars R := by
  ext; simp [RingHom.mem_ker]

/-- Over a semiring in which multiplication by `|G|` is injective (for instance an additively
torsion-free one, or one of characteristic prime to `|G|`), an element of a finite group algebra
invariant under right multiplication by every group element and with augmentation `|G| • c` is
the constant combination `∑ g, single g c`. For `c = 1` it is the norm element
`∑ g, single g 1`. -/
theorem eq_sum_single_of_mul_single_eq_self {R G : Type*} [Semiring R] [Group G] [Fintype G]
    (hG : IsSMulRegular R (Fintype.card G)) {γ : MonoidAlgebra R G} {c : R}
    (hinv : ∀ g, γ * single g 1 = γ) (hε : augmentation R G γ = Fintype.card G • c) :
    γ = ∑ g, single g c := by
  -- Right invariance makes `γ` the constant combination with coefficient `γ.coeff 1`.
  have hγ := eq_sum_single_coeff_one_of_mul_single_eq_self hinv
  -- Its augmentation is then `|G| • γ.coeff 1`, so `hε` and `hG` force `γ.coeff 1 = c`.
  have hγc : γ.coeff 1 = c := hG <| by
    rw [hγ, map_sum] at hε
    simpa using hε
  rw [hγ, hγc]

/-- Lifting the trivial character to an `R`-algebra `A` is the coefficient-sum augmentation
followed by `algebraMap R A`. -/
theorem lift_one_apply {R : Type u} [CommSemiring R] {A : Type w} [Semiring A] [Algebra R A]
    {K : Type v} [Monoid K] (x : MonoidAlgebra R K) :
    lift R A K 1 x = algebraMap R A (augmentation R K x) := by
  induction x using induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single k r => simp [lift_single, Algebra.smul_def]

end MonoidAlgebra

namespace TauCeti

/-- The augmentation of the character sum `∑_{h ∈ H} χ(h) h` is `∑_{h ∈ H} χ(h)`; for the
trivial character it is the order of `H`. -/
@[simp]
theorem augmentation_subgroupCharSum {k G : Type*} [Semiring k] [Group G] (χ : G →* k)
    (H : Subgroup G) [Fintype H] :
    MonoidAlgebra.augmentation k G (subgroupCharSum χ H) = ∑ h : H, χ (h : G) := by
  simp [subgroupCharSum_def]

end TauCeti
