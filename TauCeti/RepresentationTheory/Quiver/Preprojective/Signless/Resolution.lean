/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.KoszulComplex
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.Augmentation
public import TauCeti.RingTheory.Idempotents.Projective
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Algebra.DirectSum.Module

/-!
# Projective resolutions over the signless preprojective algebra

For a finite quiver with involutive reversal, the signless Koszul maps give a complex of right
vertex projectives. When the left Koszul map at a vertex is injective, this complex is a
length-two projective resolution of its vertex module. A non-backtracking outgoing-arrow choice
at every vertex supplies this injectivity.
The vertex module is the cokernel of the incoming-arrow map; its underlying coefficient module
is one copy of the base ring, as detected by the vertex augmentation.

Right modules are left modules over the ordinary opposite algebra. The vertex projectives are
principal left ideals in that opposite algebra, so their projectivity follows from
`IsIdempotentElem.projective_span_singleton`. Products in the original algebra are
later-factor-first: the two maps are `y ↦ (b* y)_b` and `(z_b) ↦ ∑ b z_b`.
No bipartiteness or characteristic hypothesis is used. In particular this construction applies
to the signless quadratic dual on odd cycles without identifying it with the signed algebra.
The resolution here is ungraded.

The chain-complex assembly follows
`TauCeti.RepresentationTheory.Quiver.Preprojective.Resolution`; the relations and exactness
are those of the signless Koszul complex.

## References

* S. Huerfano and M. Khovanov, *A category for the adjoint representation*, Section 3,
  for the signless quadratic dual.
* P. Etingof and C.-H. Eu, *Koszulity and the Hilbert series of preprojective algebras*,
  Sections 2 and 3, for the vertex Koszul complex.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra MulOpposite CategoryTheory

universe u v w

variable (k : Type w) [CommRing k] {R : Type u} [Quiver.{v} R]
  [Finite R] [∀ x : R, Fintype (Quiver.Star x)]

/-- A finite enumeration of vertices for the Koszul sums. -/
noncomputable local instance signlessResolutionFintypeVertex : Fintype R := Fintype.ofFinite R

/-- A finite enumeration of arrows, inherited from the outgoing star of the source. -/
noncomputable local instance signlessResolutionFintypeArrow (i j : R) : Fintype (i ⟶ j) := by
  letI : Finite (i ⟶ j) :=
    Finite.of_injective (fun b : i ⟶ j => (Quiver.Star.mk b : Quiver.Star i)) sigma_mk_injective
  exact Fintype.ofFinite _

section Reverse

variable [HasReverse R]

local notation "Π" => signlessPreprojectiveAlgebra k R
local notation "π" => signlessPreprojectiveMk k R
local notation "e" => fun i : R => π (vertexIdempotent k i)

/-- The right vertex projective `e_i Π`, as the principal left ideal of `op e_i` in `Πᵐᵒᵖ`. -/
noncomputable def signlessPreprojectiveRightProjective (i : R) : Ideal Πᵐᵒᵖ :=
  Ideal.span {op (e i)}

private theorem isIdempotentElem_op_signlessVertexIdempotent (i : R) :
    IsIdempotentElem (op (e i)) := by
  apply unop_injective
  simpa only [unop_mul, unop_op, ← map_mul] using
    congrArg π (vertexIdempotent_mul_self (k := k) i)

/-- Membership in the right vertex projective is the left corner identity in `Π`. -/
@[simp]
theorem mem_signlessPreprojectiveRightProjective_iff (i : R) (x : Πᵐᵒᵖ) :
    x ∈ signlessPreprojectiveRightProjective k i ↔ e i * unop x = unop x := by
  rw [signlessPreprojectiveRightProjective,
    mem_span_singleton_iff_mul_eq_self (isIdempotentElem_op_signlessVertexIdempotent k i),
    ← unop_inj, unop_mul, unop_op]

/-- Right vertex projectives are projective over the opposite algebra. -/
instance (i : R) : Module.Projective Πᵐᵒᵖ (signlessPreprojectiveRightProjective k i) :=
  (isIdempotentElem_op_signlessVertexIdempotent k i).projective_span_singleton

/-- The incoming-arrow term of the signless Koszul complex, a finite sum of vertex projectives. -/
abbrev signlessPreprojectiveKoszulMiddle (v : R) :=
  (i : R) → (i ⟶ v) → signlessPreprojectiveRightProjective k i

/-- The incoming-arrow term is projective as a finite direct sum. -/
instance (v : R) : Module.Projective Πᵐᵒᵖ (signlessPreprojectiveKoszulMiddle k v) := by
  let (i : R) : Module.Projective Πᵐᵒᵖ ((i ⟶ v) → signlessPreprojectiveRightProjective k i) :=
    Module.Projective.of_equiv (DirectSum.linearEquivFunOnFintype Πᵐᵒᵖ _ _)
  exact Module.Projective.of_equiv (DirectSum.linearEquivFunOnFintype Πᵐᵒᵖ _ _)

private theorem arrow_mul_mem_signlessRightProjective {i j : R} (b : i ⟶ j)
    (x : Πᵐᵒᵖ) : x * op (π (ofArrow b)) ∈ signlessPreprojectiveRightProjective k j := by
  classical
  rw [mem_signlessPreprojectiveRightProjective_iff, unop_mul, unop_op, ← mul_assoc,
    ← map_mul, vertexIdempotent_mul_ofArrow, ite_eq_left rfl]

/-- The reverse-arrow map of the signless Koszul complex, `y ↦ (b* y)_b`. -/
noncomputable def signlessPreprojectiveKoszulLeft (v : R) :
    signlessPreprojectiveRightProjective k v →ₗ[Πᵐᵒᵖ] signlessPreprojectiveKoszulMiddle k v where
  toFun y i b := ⟨(y : Πᵐᵒᵖ) * op (π (ofArrow (reverse b))),
    arrow_mul_mem_signlessRightProjective k (reverse b) y⟩
  map_add' x y := by ext i b; simp [add_mul]
  map_smul' a y := by ext i b; simp [mul_assoc]

/-- The incoming-arrow map of the signless Koszul complex, `(z_b) ↦ ∑ b z_b`. -/
noncomputable def signlessPreprojectiveKoszulRight (v : R) :
    signlessPreprojectiveKoszulMiddle k v →ₗ[Πᵐᵒᵖ] signlessPreprojectiveRightProjective k v where
  toFun z := ⟨∑ i, ∑ b : i ⟶ v, (z i b : Πᵐᵒᵖ) * op (π (ofArrow b)),
    Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun b _ =>
      arrow_mul_mem_signlessRightProjective k b (z i b)⟩
  map_add' x y := by ext; simp [add_mul, Finset.sum_add_distrib]
  map_smul' a y := by ext; simp [mul_assoc, Finset.mul_sum]

@[simp]
theorem unop_signlessPreprojectiveKoszulLeft_apply (v : R)
    (y : signlessPreprojectiveRightProjective k v) (i : R) (b : i ⟶ v) :
    unop (signlessPreprojectiveKoszulLeft k v y i b : Πᵐᵒᵖ) =
      π (ofArrow (reverse b)) * unop (y : Πᵐᵒᵖ) := by
  exact unop_mul _ _

@[simp]
theorem unop_signlessPreprojectiveKoszulRight_apply (v : R)
    (z : signlessPreprojectiveKoszulMiddle k v) :
    unop (signlessPreprojectiveKoszulRight k v z : Πᵐᵒᵖ) =
      ∑ i, ∑ b : i ⟶ v, π (ofArrow b) * unop (z i b : Πᵐᵒᵖ) := by
  simp [signlessPreprojectiveKoszulRight]

/-- The vertex module, defined as the cokernel of the incoming-arrow map. -/
abbrev signlessPreprojectiveVertexModule (v : R) :=
  signlessPreprojectiveRightProjective k v ⧸ LinearMap.range (signlessPreprojectiveKoszulRight k v)

/-- The vertex augmentation, as a homomorphism of right signless modules. -/
noncomputable def signlessPreprojectiveVertexAugmentation (v : R) :
    signlessPreprojectiveRightProjective k v →ₗ[Πᵐᵒᵖ] signlessPreprojectiveVertexModule k v :=
  (LinearMap.range (signlessPreprojectiveKoszulRight k v)).mkQ

/-- The vertex augmentation is the quotient-class map. -/
theorem signlessPreprojectiveVertexAugmentation_apply (v : R)
    (x : signlessPreprojectiveRightProjective k v) :
    signlessPreprojectiveVertexAugmentation k v x = Submodule.Quotient.mk x := (rfl)

/-- The incoming-arrow image is exactly the kernel of the vertex augmentation. -/
@[simp]
theorem ker_signlessPreprojectiveVertexAugmentation (v : R) :
    LinearMap.ker (signlessPreprojectiveVertexAugmentation k v) =
      LinearMap.range (signlessPreprojectiveKoszulRight k v) := Submodule.ker_mkQ _

/-- Every vertex-module class lifts to the right vertex projective. -/
theorem signlessPreprojectiveVertexAugmentation_surjective (v : R) :
    Function.Surjective (signlessPreprojectiveVertexAugmentation k v) := Submodule.mkQ_surjective _

/-- The quotient kills exactly the elements with zero coefficient at the specified vertex. -/
@[simp]
theorem signlessPreprojectiveVertexAugmentation_eq_zero_iff (v : R)
    (x : signlessPreprojectiveRightProjective k v) :
    signlessPreprojectiveVertexAugmentation k v x = 0 ↔
      signlessPreprojectiveAugmentation k (unop (x : Πᵐᵒᵖ)) v = 0 := by
  rw [signlessPreprojectiveVertexAugmentation, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
  rw [signlessPreprojectiveAugmentation_apply_eq_zero_iff_exists_eq_sum k v
    ((mem_signlessPreprojectiveRightProjective_iff k v _).1 x.property)]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨fun i b => unop (z i b : Πᵐᵒᵖ), fun i b =>
      (mem_signlessPreprojectiveRightProjective_iff k i _).1 (z i b).property,
      unop_signlessPreprojectiveKoszulRight_apply k v z⟩
  · rintro ⟨z, hz, hxz⟩
    refine ⟨fun i b => ⟨op (z i b), (mem_signlessPreprojectiveRightProjective_iff k i _).2
      (hz i b)⟩, Subtype.ext (unop_injective ?_)⟩
    simpa only [unop_signlessPreprojectiveKoszulRight_apply, unop_op] using hxz.symm

/-! ### The coefficient module of a vertex -/

private noncomputable def signlessVertexCoeff (v : R) :
    signlessPreprojectiveRightProjective k v →ₗ[k] k :=
  (LinearMap.proj v).comp ((signlessPreprojectiveAugmentation k).toLinearMap.comp
    ((opLinearEquiv k (M := Π)).symm.toLinearMap.comp
      ((signlessPreprojectiveRightProjective k v).subtype.restrictScalars k)))

private theorem signlessVertexCoeff_apply (v : R) (x : signlessPreprojectiveRightProjective k v) :
    signlessVertexCoeff k v x = signlessPreprojectiveAugmentation k (unop (x : Πᵐᵒᵖ)) v := (rfl)

private theorem signlessVertexCoeff_surjective (v : R) :
    Function.Surjective (signlessVertexCoeff k v) := by
  intro c
  obtain ⟨x, hx, hxc⟩ := exists_signlessPreprojectiveAugmentation_apply_eq k v c
  exact ⟨⟨op x, (mem_signlessPreprojectiveRightProjective_iff k v _).2 hx⟩, hxc⟩

private theorem range_signlessKoszulRight_restrictScalars_eq_ker_coeff (v : R) :
    (LinearMap.range (signlessPreprojectiveKoszulRight k v)).restrictScalars k =
      LinearMap.ker (signlessVertexCoeff k v) := by
  ext x
  rw [Submodule.restrictScalars_mem, ← ker_signlessPreprojectiveVertexAugmentation,
    LinearMap.mem_ker, signlessPreprojectiveVertexAugmentation_eq_zero_iff,
    LinearMap.mem_ker, signlessVertexCoeff_apply]

/-- The underlying coefficient module of the right vertex module is one copy of `k`,
identified by its vertex coefficient. -/
noncomputable def signlessPreprojectiveVertexModuleEquiv (v : R) :
    signlessPreprojectiveVertexModule k v ≃ₗ[k] k :=
  (Submodule.Quotient.restrictScalarsEquiv k
    (LinearMap.range (signlessPreprojectiveKoszulRight k v))).symm.trans
    ((Submodule.quotEquivOfEq _ _
      (range_signlessKoszulRight_restrictScalars_eq_ker_coeff k v)).trans
      ((signlessVertexCoeff k v).quotKerEquivOfSurjective (signlessVertexCoeff_surjective k v)))

/-- The coefficient-module equivalence sends a quotient class to its vertex coefficient. -/
@[simp]
theorem signlessPreprojectiveVertexModuleEquiv_augmentation (v : R)
    (x : signlessPreprojectiveRightProjective k v) :
    signlessPreprojectiveVertexModuleEquiv k v
        (signlessPreprojectiveVertexAugmentation k v x) =
      signlessPreprojectiveAugmentation k (unop (x : Πᵐᵒᵖ)) v := by
  simp only [signlessPreprojectiveVertexModuleEquiv,
    signlessPreprojectiveVertexAugmentation_apply, LinearEquiv.trans_apply,
    Submodule.Quotient.restrictScalarsEquiv_symm_mk, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk, signlessVertexCoeff_apply]

/-- The inverse coefficient equivalence sends a vertex coefficient back to its quotient class. -/
@[simp]
theorem signlessPreprojectiveVertexModuleEquiv_symm_coeff (v : R)
    (x : signlessPreprojectiveRightProjective k v) :
    (signlessPreprojectiveVertexModuleEquiv k v).symm
        (signlessPreprojectiveAugmentation k (unop (x : Πᵐᵒᵖ)) v) =
      signlessPreprojectiveVertexAugmentation k v x := by
  rw [← signlessPreprojectiveVertexModuleEquiv_augmentation, LinearEquiv.symm_apply_apply]

/-- Under the coefficient equivalence, the right algebra action is evaluation of the
augmentation at the specified vertex. -/
@[simp]
theorem signlessPreprojectiveVertexModuleEquiv_smul (v : R) (a : Πᵐᵒᵖ)
    (x : signlessPreprojectiveVertexModule k v) :
    signlessPreprojectiveVertexModuleEquiv k v (a • x) =
      signlessPreprojectiveAugmentation k (unop a) v *
        signlessPreprojectiveVertexModuleEquiv k v x := by
  obtain ⟨y, rfl⟩ := signlessPreprojectiveVertexAugmentation_surjective k v x
  rw [← map_smul, signlessPreprojectiveVertexModuleEquiv_augmentation,
    signlessPreprojectiveVertexModuleEquiv_augmentation]
  simp only [Submodule.coe_smul, smul_eq_mul, unop_mul, map_mul, Pi.mul_apply, mul_comm]

end Reverse

section InvolutiveReverse

variable [HasInvolutiveReverse R]

local notation "Π" => signlessPreprojectiveAlgebra k R
local notation "π" => signlessPreprojectiveMk k R

/-- The signless relation makes the composite of the Koszul maps zero. -/
@[simp]
theorem signlessPreprojectiveKoszulRight_comp_left (v : R) :
    (signlessPreprojectiveKoszulRight k v).comp (signlessPreprojectiveKoszulLeft k v) = 0 := by
  ext y
  apply unop_injective
  simpa only [LinearMap.comp_apply, unop_signlessPreprojectiveKoszulRight_apply,
    unop_signlessPreprojectiveKoszulLeft_apply, LinearMap.zero_apply, Submodule.coe_zero,
    unop_zero] using sum_signlessPreprojectiveMk_ofArrow_mul_ofArrow_reverse_mul_eq_zero k v
      (unop (y : Πᵐᵒᵖ))

/-- Exactness at the incoming-arrow term holds for every finite quiver with involutive reversal. -/
theorem range_signlessPreprojectiveKoszulLeft_eq_ker_right (v : R) :
    LinearMap.range (signlessPreprojectiveKoszulLeft k v) =
      LinearMap.ker (signlessPreprojectiveKoszulRight k v) := by
  ext z
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun (signlessPreprojectiveKoszulRight_comp_left k v) y
  · intro hz
    have hz' := congrArg (fun x : signlessPreprojectiveRightProjective k v => unop (x : Πᵐᵒᵖ)) hz
    rw [unop_signlessPreprojectiveKoszulRight_apply, Submodule.coe_zero, unop_zero] at hz'
    obtain ⟨y, hy, hzy⟩ := (sum_signlessPreprojectiveMk_ofArrow_mul_eq_zero_iff k v
      (fun i b => (mem_signlessPreprojectiveRightProjective_iff k i _).1 (z i b).property)).1 hz'
    refine ⟨⟨op y, (mem_signlessPreprojectiveRightProjective_iff k v _).2 hy⟩, ?_⟩
    exact funext fun i => funext fun b => Subtype.ext (unop_injective (by
      rw [unop_signlessPreprojectiveKoszulLeft_apply, unop_op, hzy]))

/-- A non-backtracking outgoing-arrow choice makes the left Koszul map injective. -/
theorem signlessPreprojectiveKoszulLeft_injective {σ : ∀ v : R, Quiver.Star v}
    (hσ : ∀ v, σ (σ v).1 ≠ Quiver.Star.mk (reverse (σ v).2)) (v : R) :
    Function.Injective (signlessPreprojectiveKoszulLeft k v) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  apply Subtype.ext
  apply unop_injective
  apply (forall_signlessPreprojectiveMk_ofArrow_reverse_mul_eq_zero_iff_of_ne_reverse k hσ v
    ((mem_signlessPreprojectiveRightProjective_iff k v _).1 y.property)).1
  intro i b
  simpa only [unop_signlessPreprojectiveKoszulLeft_apply, Pi.zero_apply, Submodule.coe_zero,
    unop_zero] using congrArg (fun z => unop (z i b : Πᵐᵒᵖ)) hy

/-! ### The augmented chain complex -/

/-- The signless Koszul terms: the vertex projective in degrees zero and two, the
incoming-arrow projective in degree one, and zero thereafter. -/
noncomputable abbrev signlessPreprojectiveKoszulTerm (v : R) : ℕ → ModuleCat.{max u v w} Πᵐᵒᵖ
  | 0 => ModuleCat.of _ (signlessPreprojectiveRightProjective k v)
  | 1 => ModuleCat.of _ (signlessPreprojectiveKoszulMiddle k v)
  | 2 => ModuleCat.of _ (signlessPreprojectiveRightProjective k v)
  | _ + 3 => ModuleCat.of _ PUnit

/-- The signless Koszul differentials in consecutive homological degrees. -/
noncomputable def signlessPreprojectiveKoszulDifferential (v : R) : ∀ n : ℕ,
    signlessPreprojectiveKoszulTerm k v (n + 1) ⟶ signlessPreprojectiveKoszulTerm k v n
  | 0 => ModuleCat.ofHom (signlessPreprojectiveKoszulRight k v)
  | 1 => ModuleCat.ofHom (signlessPreprojectiveKoszulLeft k v)
  | _ + 2 => 0

@[simp]
theorem signlessPreprojectiveKoszulDifferential_zero (v : R) :
    signlessPreprojectiveKoszulDifferential k v 0 =
      ModuleCat.ofHom (signlessPreprojectiveKoszulRight k v) := (rfl)

@[simp]
theorem signlessPreprojectiveKoszulDifferential_one (v : R) :
    signlessPreprojectiveKoszulDifferential k v 1 =
      ModuleCat.ofHom (signlessPreprojectiveKoszulLeft k v) := (rfl)

@[simp]
theorem signlessPreprojectiveKoszulDifferential_add_two (v : R) (n : ℕ) :
    signlessPreprojectiveKoszulDifferential k v (n + 2) = 0 := (rfl)

private theorem signlessPreprojectiveKoszulDifferential_comp_succ (v : R) : ∀ n : ℕ,
    signlessPreprojectiveKoszulDifferential k v (n + 1) ≫
      signlessPreprojectiveKoszulDifferential k v n = 0
  | 0 => by
    apply ModuleCat.hom_ext
    exact signlessPreprojectiveKoszulRight_comp_left k v
  | 1 => by simp [signlessPreprojectiveKoszulDifferential]
  | _ + 2 => by simp [signlessPreprojectiveKoszulDifferential]

/-- The right-module Koszul chain complex over the signless preprojective algebra. -/
noncomputable def signlessPreprojectiveKoszulComplex (v : R) :
    ChainComplex (ModuleCat.{max u v w} Πᵐᵒᵖ) ℕ :=
  ChainComplex.of (signlessPreprojectiveKoszulTerm k v)
    (signlessPreprojectiveKoszulDifferential k v)
    (signlessPreprojectiveKoszulDifferential_comp_succ k v)

/-- Identification of the bundled complex terms with the explicit vertex and arrow projectives. -/
noncomputable def signlessPreprojectiveKoszulComplexXIso (v : R) (n : ℕ) :
    (signlessPreprojectiveKoszulComplex k v).X n ≅ signlessPreprojectiveKoszulTerm k v n :=
  Iso.refl _

/-- The bundled differential is the explicit incoming-arrow or reverse-arrow map. -/
@[simp]
theorem signlessPreprojectiveKoszulComplex_d (v : R) (n : ℕ) :
    (signlessPreprojectiveKoszulComplex k v).d (n + 1) n =
      (signlessPreprojectiveKoszulComplexXIso k v (n + 1)).hom ≫
        signlessPreprojectiveKoszulDifferential k v n ≫
          (signlessPreprojectiveKoszulComplexXIso k v n).inv := ChainComplex.of_d _ _ _

private noncomputable def signlessPreprojectiveKoszulComplexπ (v : R) :
    signlessPreprojectiveKoszulComplex k v ⟶
      (ChainComplex.single₀ _).obj (ModuleCat.of Πᵐᵒᵖ (signlessPreprojectiveVertexModule k v)) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨ModuleCat.ofHom (signlessPreprojectiveVertexAugmentation k v), by
      apply ModuleCat.hom_ext
      exact LinearMap.range_mkQ_comp (signlessPreprojectiveKoszulRight k v)⟩

private theorem signlessPreprojectiveKoszulComplexπ_f_zero (v : R) :
    (signlessPreprojectiveKoszulComplexπ k v).f 0 =
      ModuleCat.ofHom (signlessPreprojectiveVertexAugmentation k v) :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

private theorem range_signlessPreprojectiveKoszulDifferential_succ_eq_ker
    (v : R) (hinj : Function.Injective (signlessPreprojectiveKoszulLeft k v)) : ∀ n : ℕ,
    LinearMap.range (signlessPreprojectiveKoszulDifferential k v (n + 1)).hom =
      LinearMap.ker (signlessPreprojectiveKoszulDifferential k v n).hom
  | 0 => range_signlessPreprojectiveKoszulLeft_eq_ker_right k v
  | 1 => by
    simp only [signlessPreprojectiveKoszulDifferential, ModuleCat.hom_zero, LinearMap.range_zero]
    exact ((LinearMap.ker_eq_bot).2 hinj).symm
  | n + 2 => by
    ext x
    have hx : x = 0 := Subsingleton.elim x 0
    simp [signlessPreprojectiveKoszulDifferential, hx]

/-- Injectivity of the left Koszul map gives a length-two projective resolution of the
right vertex module of the signless preprojective algebra. -/
noncomputable def signlessPreprojectiveKoszulProjectiveResolution (v : R)
    (hinj : Function.Injective (signlessPreprojectiveKoszulLeft k v)) :
    ProjectiveResolution (ModuleCat.of Πᵐᵒᵖ (signlessPreprojectiveVertexModule k v)) where
  complex := signlessPreprojectiveKoszulComplex k v
  projective n := by
    rcases n with _ | (_ | (_ | n))
    · exact inferInstanceAs (Projective (ModuleCat.of Πᵐᵒᵖ
        (signlessPreprojectiveRightProjective k v)))
    · exact inferInstanceAs (Projective (ModuleCat.of Πᵐᵒᵖ
        (signlessPreprojectiveKoszulMiddle k v)))
    · exact inferInstanceAs (Projective (ModuleCat.of Πᵐᵒᵖ
        (signlessPreprojectiveRightProjective k v)))
    · exact (ModuleCat.isZero_of_subsingleton (ModuleCat.of Πᵐᵒᵖ PUnit)).projective
  «π» := signlessPreprojectiveKoszulComplexπ k v
  quasiIso := by
    constructor
    intro n
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros' _ rfl rfl rfl]
      refine ⟨?_, ?_⟩
      · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
        simp only [HomologicalComplex.shortComplexFunctor'_obj_f]
        exact (ker_signlessPreprojectiveVertexAugmentation k v).symm
      · rw [ModuleCat.epi_iff_surjective]
        exact signlessPreprojectiveVertexAugmentation_surjective k v
    | succ n =>
      rw [quasiIsoAt_iff_exactAt' (hL := ChainComplex.exactAt_succ_single_obj ..),
        HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp),
        ShortComplex.moduleCat_exact_iff_range_eq_ker]
      -- Identify the short-complex wrapper's module instances with the explicit terms
      -- so `ChainComplex.of_d` can compute both maps.
      change LinearMap.range (ChainComplex.of.d (signlessPreprojectiveKoszulTerm k v)
        (signlessPreprojectiveKoszulDifferential k v) (n + 1 + 1) (n + 1)).hom =
          LinearMap.ker (ChainComplex.of.d (signlessPreprojectiveKoszulTerm k v)
            (signlessPreprojectiveKoszulDifferential k v) (n + 1) n).hom
      rw [ChainComplex.of_d (signlessPreprojectiveKoszulTerm k v)
        (signlessPreprojectiveKoszulDifferential k v) (n + 1),
        ChainComplex.of_d (signlessPreprojectiveKoszulTerm k v)
          (signlessPreprojectiveKoszulDifferential k v) n]
      exact range_signlessPreprojectiveKoszulDifferential_succ_eq_ker k v hinj n

/-- The projective resolution uses the explicit signless Koszul complex. -/
@[simp]
theorem signlessPreprojectiveKoszulProjectiveResolution_complex (v : R)
    (hinj : Function.Injective (signlessPreprojectiveKoszulLeft k v)) :
    (signlessPreprojectiveKoszulProjectiveResolution k v hinj).complex =
      signlessPreprojectiveKoszulComplex k v := (rfl)

/-- The terms of the projective resolution identified with the explicit Koszul terms. -/
noncomputable def signlessPreprojectiveKoszulProjectiveResolutionXIso
    (v : R) (hinj : Function.Injective (signlessPreprojectiveKoszulLeft k v)) (n : ℕ) :
    (signlessPreprojectiveKoszulProjectiveResolution k v hinj).complex.X n ≅
      signlessPreprojectiveKoszulTerm k v n :=
  eqToIso (congrArg (fun C => C.X n)
    (signlessPreprojectiveKoszulProjectiveResolution_complex k v hinj)) ≪≫
      signlessPreprojectiveKoszulComplexXIso k v n

/-- The differentials of the projective resolution are the explicit Koszul maps, using
its term identifications. -/
@[simp]
theorem signlessPreprojectiveKoszulProjectiveResolution_d
    (v : R) (hinj : Function.Injective (signlessPreprojectiveKoszulLeft k v)) (n : ℕ) :
    (signlessPreprojectiveKoszulProjectiveResolution k v hinj).complex.d (n + 1) n =
      (signlessPreprojectiveKoszulProjectiveResolutionXIso k v hinj (n + 1)).hom ≫
        signlessPreprojectiveKoszulDifferential k v n ≫
          (signlessPreprojectiveKoszulProjectiveResolutionXIso k v hinj n).inv := by
  -- The term identifications are identities after expanding the constructed resolution.
  dsimp only [signlessPreprojectiveKoszulProjectiveResolutionXIso,
    signlessPreprojectiveKoszulProjectiveResolution, eqToIso_refl, Iso.trans_refl]
  exact signlessPreprojectiveKoszulComplex_d k v n

/-- The augmentation of the resolution is the vertex quotient map. -/
@[simp]
theorem signlessPreprojectiveKoszulProjectiveResolution_π_f_zero
    (v : R) (hinj : Function.Injective (signlessPreprojectiveKoszulLeft k v)) :
    (signlessPreprojectiveKoszulProjectiveResolutionXIso k v hinj 0).inv ≫
        (signlessPreprojectiveKoszulProjectiveResolution k v hinj).π.f 0 =
      ModuleCat.ofHom (signlessPreprojectiveVertexAugmentation k v) := by
  -- The resolution and term identifications reduce to identities by construction.
  dsimp only [signlessPreprojectiveKoszulProjectiveResolutionXIso,
    signlessPreprojectiveKoszulProjectiveResolution, eqToIso_refl, Iso.trans_refl]
  exact signlessPreprojectiveKoszulComplexπ_f_zero k v

end InvolutiveReverse

end TauCeti
