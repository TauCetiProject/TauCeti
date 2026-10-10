/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.KoszulComplex
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Sinkless
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
import Mathlib.Algebra.DirectSum.Module

/-!
# Projective resolutions of preprojective vertex modules

For a finite quiver `Q`, write `Π = Π_k(Q)`. The right vertex projective `e_v Π` consists of
path classes ending at `v`. Right modules are represented as left modules over `Πᵐᵒᵖ`.
This file bundles the two maps of the preprojective Koszul complex as right-module maps:

`e_v Π → ⨁_{b : i → v} e_i Π → e_v Π`,

with formulas `y ↦ (ε_b b* y)_b` and `(z_b) ↦ ∑_b b z_b`. Multiplication is
later-factor-first. The finite direct sum is implemented as a dependent function space.
The cokernel is the vertex augmentation module: the kernel of its quotient map is precisely
the positive path-degree part of `e_v Π`.

The middle exactness is valid over every commutative ring and for every finite quiver.
When every vertex of `Q` has an outgoing arrow, the first map is injective and the augmented
complex is a length-two projective resolution. The construction uses the exactness theorems in
`TauCeti.RepresentationTheory.Quiver.Preprojective.KoszulComplex` and the injectivity theorem in
`TauCeti.RepresentationTheory.Quiver.Preprojective.Sinkless`. This is an ungraded resolution;
internal shifts and linearity are not asserted here.

## References

* P. Etingof and C.-H. Eu, *Koszulity and the Hilbert series of preprojective algebras*,
  Math. Res. Lett. 14 (2007), Sections 2 and 3.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra MulOpposite CategoryTheory

universe u v w

variable (k : Type w) {Q : Type u} [CommRing k] [Quiver.{v} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

local notation "Π" => preprojectiveAlgebra k Q
local notation "π" => preprojectiveMk k Q
local notation "e" => fun i : Symmetrify Q => π (vertexIdempotent k i)

/-- The right vertex projective `e_i Π`, realized inside `Π` with opposite scalars. -/
noncomputable def preprojectiveRightProjective (i : Symmetrify Q) : Submodule Πᵐᵒᵖ Π :=
  LinearMap.range (LinearMap.mulLeft Πᵐᵒᵖ (e i))

/-- A path class belongs to `e_i Π` exactly when left multiplication by `e_i` fixes it. -/
@[simp]
theorem mem_preprojectiveRightProjective_iff (i : Symmetrify Q) (x : Π) :
    x ∈ preprojectiveRightProjective k i ↔ e i * x = x := by
  have he : e i * e i = e i := by rw [← map_mul, vertexIdempotent_mul_self]
  constructor
  · rintro ⟨y, rfl⟩
    simp only [LinearMap.mulLeft_apply, ← mul_assoc, he]
  · intro hx
    exact ⟨x, hx⟩

/-- Each right vertex ideal is projective, since multiplication by its idempotent splits its
inclusion in the regular right module. -/
instance (i : Symmetrify Q) : Module.Projective Πᵐᵒᵖ (preprojectiveRightProjective k i) := by
  let : Module.Projective Πᵐᵒᵖ Π :=
    Module.Projective.of_equiv (MulOpposite.opLinearEquiv Πᵐᵒᵖ (M := Π)).symm
  refine Module.Projective.of_split (preprojectiveRightProjective k i).subtype
    (LinearMap.mulLeft Πᵐᵒᵖ (e i)).rangeRestrict ?_
  ext x
  exact (mem_preprojectiveRightProjective_iff k i x).1 x.property

/-- The middle projective of the Koszul complex at `v`, indexed by doubled arrows into `v`. -/
abbrev preprojectiveKoszulMiddle (v : Q) :=
  (i : Symmetrify Q) → (i ⟶ Symmetrify.of.obj v) → preprojectiveRightProjective k i

instance (v : Q) : Module.Projective Πᵐᵒᵖ (preprojectiveKoszulMiddle k v) := by
  let (i : Symmetrify Q) :
      Module.Projective Πᵐᵒᵖ ((i ⟶ Symmetrify.of.obj v) → preprojectiveRightProjective k i) :=
    Module.Projective.of_equiv (DirectSum.linearEquivFunOnFintype Πᵐᵒᵖ _ _)
  exact Module.Projective.of_equiv (DirectSum.linearEquivFunOnFintype Πᵐᵒᵖ _ _)

private theorem arrow_mul_mem_rightProjective {i j : Symmetrify Q} (b : i ⟶ j) (x : Π) :
    π (ofArrow b) * x ∈ preprojectiveRightProjective k j := by
  classical
  rw [mem_preprojectiveRightProjective_iff, ← mul_assoc, ← map_mul,
    vertexIdempotent_mul_ofArrow, ite_eq_left rfl]

/-- The first Koszul differential, `y ↦ (ε_b b* y)_b`. -/
noncomputable def preprojectiveKoszulLeft (v : Q) :
    preprojectiveRightProjective k (Symmetrify.of.obj v) →ₗ[Πᵐᵒᵖ]
      preprojectiveKoszulMiddle k v where
  toFun y i b := ⟨doubledArrowSign k b • (π (ofArrow (Quiver.reverse b)) * y), by
    rw [mem_preprojectiveRightProjective_iff, mul_smul_comm]
    exact congrArg (doubledArrowSign k b • ·)
      ((mem_preprojectiveRightProjective_iff k i _).1
        (arrow_mul_mem_rightProjective k (Quiver.reverse b) y))⟩
  map_add' x y := by ext i b; simp [mul_add, smul_add]
  map_smul' a y := by
    ext i b
    simp [MulOpposite.smul_eq_mul_unop, mul_assoc]

/-- The second Koszul differential, `(z_b) ↦ ∑_b b z_b`. -/
noncomputable def preprojectiveKoszulRight (v : Q) :
    preprojectiveKoszulMiddle k v →ₗ[Πᵐᵒᵖ]
      preprojectiveRightProjective k (Symmetrify.of.obj v) where
  toFun z := ⟨∑ i, ∑ b : i ⟶ Symmetrify.of.obj v, π (ofArrow b) * z i b,
    Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun b _ =>
      arrow_mul_mem_rightProjective k b (z i b)⟩
  map_add' x y := by ext; simp [mul_add, Finset.sum_add_distrib]
  map_smul' a y := by
    ext
    simp [MulOpposite.smul_eq_mul_unop, mul_assoc, Finset.sum_mul]

@[simp]
theorem coe_preprojectiveKoszulLeft_apply (v : Q)
    (y : preprojectiveRightProjective k (Symmetrify.of.obj v)) (i : Symmetrify Q)
    (b : i ⟶ Symmetrify.of.obj v) :
    (preprojectiveKoszulLeft k v y i b : Π) =
      doubledArrowSign k b • (π (ofArrow (Quiver.reverse b)) * y) := (rfl)

@[simp]
theorem coe_preprojectiveKoszulRight_apply (v : Q) (z : preprojectiveKoszulMiddle k v) :
    (preprojectiveKoszulRight k v z : Π) =
      ∑ i, ∑ b : i ⟶ Symmetrify.of.obj v, π (ofArrow b) * z i b := (rfl)

/-- The Koszul differentials compose to zero by the local preprojective relation. -/
@[simp]
theorem preprojectiveKoszulRight_comp_left (v : Q) :
    (preprojectiveKoszulRight k v).comp (preprojectiveKoszulLeft k v) = 0 := by
  ext y
  exact sum_preprojectiveMk_ofArrow_mul_doubledArrowSign_smul_eq_zero k v y

/-- Exactness at the middle projective, with no restriction on the quiver. -/
theorem range_preprojectiveKoszulLeft_eq_ker_right (v : Q) :
    LinearMap.range (preprojectiveKoszulLeft k v) =
      LinearMap.ker (preprojectiveKoszulRight k v) := by
  ext z
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun (preprojectiveKoszulRight_comp_left k v) y
  · intro hz
    have hz' : ∑ i, ∑ b : i ⟶ Symmetrify.of.obj v, π (ofArrow b) * (z i b : Π) = 0 :=
      congrArg Subtype.val hz
    obtain ⟨y, hy, hzy⟩ := (sum_preprojectiveMk_ofArrow_mul_eq_zero_iff k v
      (fun i b => (mem_preprojectiveRightProjective_iff k i _).1 (z i b).property)).1 hz'
    rw [doubledVertexIdempotent_def] at hy
    exact ⟨⟨y, (mem_preprojectiveRightProjective_iff k _ _).2 hy⟩,
      funext fun i => funext fun b => Subtype.ext (hzy i b).symm⟩

/-- The vertex augmentation module, the cokernel of the incoming-arrow map on `e_v Π`.
Its quotient kernel is precisely the positive path-degree part. -/
abbrev preprojectiveVertexModule (v : Q) :=
  preprojectiveRightProjective k (Symmetrify.of.obj v) ⧸
    LinearMap.range (preprojectiveKoszulRight k v)

/-- The augmentation from the vertex projective to its vertex module. -/
noncomputable def preprojectiveVertexAugmentation (v : Q) :
    preprojectiveRightProjective k (Symmetrify.of.obj v) →ₗ[Πᵐᵒᵖ]
      preprojectiveVertexModule k v :=
  (LinearMap.range (preprojectiveKoszulRight k v)).mkQ

/-- The augmentation kills exactly the elements of positive path degree. -/
@[simp]
theorem preprojectiveVertexAugmentation_eq_zero_iff (v : Q)
    (x : preprojectiveRightProjective k (Symmetrify.of.obj v)) :
    preprojectiveVertexAugmentation k v x = 0 ↔ (x : Π) ∈ ⨆ n, preprojectiveGrade k Q (n + 1) := by
  rw [preprojectiveVertexAugmentation, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    LinearMap.mem_range]
  have hx : π (doubledVertexIdempotent k v) * (x : Π) = x := by
    simpa only [doubledVertexIdempotent_def] using
      (mem_preprojectiveRightProjective_iff k _ _).1 x.property
  rw [mem_iSup_preprojectiveGrade_add_one_iff_exists_eq_sum k v hx]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨fun i b => z i b, fun i b =>
      (mem_preprojectiveRightProjective_iff k i _).1 (z i b).property, rfl⟩
  · rintro ⟨z, hz, hxz⟩
    exact ⟨fun i b => ⟨z i b, (mem_preprojectiveRightProjective_iff k i _).2 (hz i b)⟩,
      Subtype.ext hxz.symm⟩

@[simp]
theorem ker_preprojectiveVertexAugmentation (v : Q) :
    LinearMap.ker (preprojectiveVertexAugmentation k v) =
      LinearMap.range (preprojectiveKoszulRight k v) :=
  Submodule.ker_mkQ _

/-- The vertex augmentation is surjective. -/
theorem preprojectiveVertexAugmentation_surjective (v : Q) :
    Function.Surjective (preprojectiveVertexAugmentation k v) :=
  Submodule.mkQ_surjective _

/-- For a quiver without sinks, the left Koszul differential is injective. -/
theorem preprojectiveKoszulLeft_injective (hQ : ∀ u : Q, ∃ w, Nonempty (u ⟶ w)) (v : Q) :
    Function.Injective (preprojectiveKoszulLeft k v) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  apply Subtype.ext
  have hv : π (doubledVertexIdempotent k v) * (y : Π) = y := by
    simpa only [doubledVertexIdempotent_def] using
      (mem_preprojectiveRightProjective_iff k _ _).1 y.property
  apply (forall_preprojectiveMk_ofArrow_reverse_mul_eq_zero_iff k hQ v hv).1
  intro i b
  have hb : doubledArrowSign k b • (π (ofArrow (Quiver.reverse b)) * (y : Π)) = 0 :=
    congrArg (fun z => (z i b : Π)) hy
  have hh := congrArg (doubledArrowSign k b • ·) hb
  simpa only [smul_smul, doubledArrowSign_mul_self, one_smul, smul_zero] using hh

/-! ### The augmented chain complex -/

/-- The projective terms of the vertex Koszul complex: `e_v Π` in degrees zero and two,
the incoming-arrow projective in degree one, and zero thereafter. -/
noncomputable abbrev preprojectiveKoszulTerm (v : Q) : ℕ → ModuleCat.{max u v w} Πᵐᵒᵖ
  | 0 => ModuleCat.of _ (preprojectiveRightProjective k (Symmetrify.of.obj v))
  | 1 => ModuleCat.of _ (preprojectiveKoszulMiddle k v)
  | 2 => ModuleCat.of _ (preprojectiveRightProjective k (Symmetrify.of.obj v))
  | _ + 3 => ModuleCat.of _ PUnit

/-- The differentials of the vertex Koszul chain complex. -/
noncomputable def preprojectiveKoszulDifferential (v : Q) : ∀ n : ℕ,
    preprojectiveKoszulTerm k v (n + 1) ⟶ preprojectiveKoszulTerm k v n
  | 0 => ModuleCat.ofHom (preprojectiveKoszulRight k v)
  | 1 => ModuleCat.ofHom (preprojectiveKoszulLeft k v)
  | _ + 2 => 0

@[simp]
theorem preprojectiveKoszulDifferential_zero (v : Q) :
    preprojectiveKoszulDifferential k v 0 = ModuleCat.ofHom (preprojectiveKoszulRight k v) :=
  (rfl)

@[simp]
theorem preprojectiveKoszulDifferential_one (v : Q) :
    preprojectiveKoszulDifferential k v 1 = ModuleCat.ofHom (preprojectiveKoszulLeft k v) :=
  (rfl)

@[simp]
theorem preprojectiveKoszulDifferential_add_two (v : Q) (n : ℕ) :
    preprojectiveKoszulDifferential k v (n + 2) = 0 := (rfl)

private theorem preprojectiveKoszulDifferential_comp_succ (v : Q) : ∀ n : ℕ,
    preprojectiveKoszulDifferential k v (n + 1) ≫ preprojectiveKoszulDifferential k v n = 0
  | 0 => by
    apply ModuleCat.hom_ext
    exact preprojectiveKoszulRight_comp_left k v
  | 1 => by simp [preprojectiveKoszulDifferential]
  | _ + 2 => by simp [preprojectiveKoszulDifferential]

/-- The right-module Koszul chain complex of a vertex of the preprojective algebra. -/
noncomputable def preprojectiveKoszulComplex (v : Q) :
    ChainComplex (ModuleCat.{max u v w} Πᵐᵒᵖ) ℕ :=
  ChainComplex.of (preprojectiveKoszulTerm k v) (preprojectiveKoszulDifferential k v)
    (preprojectiveKoszulDifferential_comp_succ k v)

/-- The terms of the bundled complex, identified with the explicit projective terms. -/
noncomputable def preprojectiveKoszulComplexXIso (v : Q) (n : ℕ) :
    (preprojectiveKoszulComplex k v).X n ≅ preprojectiveKoszulTerm k v n :=
  Iso.refl _

/-- The differential of the bundled complex is the specified Koszul differential. -/
@[simp]
theorem preprojectiveKoszulComplex_d (v : Q) (n : ℕ) :
    (preprojectiveKoszulComplex k v).d (n + 1) n =
      (preprojectiveKoszulComplexXIso k v (n + 1)).hom ≫
        preprojectiveKoszulDifferential k v n ≫ (preprojectiveKoszulComplexXIso k v n).inv :=
  ChainComplex.of_d _ _ _

private noncomputable def preprojectiveKoszulComplexπ (v : Q) :
    preprojectiveKoszulComplex k v ⟶
      (ChainComplex.single₀ _).obj (ModuleCat.of Πᵐᵒᵖ (preprojectiveVertexModule k v)) :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨ModuleCat.ofHom (preprojectiveVertexAugmentation k v), by
    apply ModuleCat.hom_ext
    ext z
    -- The chain-complex wrapper retains its object instances; identify the composite
    -- before rewriting its kernel in the concrete vertex projective.
    change preprojectiveVertexAugmentation k v (preprojectiveKoszulRight k v z) = 0
    apply LinearMap.mem_ker.1
    rw [ker_preprojectiveVertexAugmentation]
    exact LinearMap.mem_range_self _ z⟩

private theorem preprojectiveKoszulComplexπ_f_zero (v : Q) :
    (preprojectiveKoszulComplexπ k v).f 0 = ModuleCat.ofHom (preprojectiveVertexAugmentation k v) :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

private theorem range_preprojectiveKoszulDifferential_succ_eq_ker
    (hQ : ∀ u : Q, ∃ w, Nonempty (u ⟶ w)) (v : Q) : ∀ n : ℕ,
    LinearMap.range (preprojectiveKoszulDifferential k v (n + 1)).hom =
      LinearMap.ker (preprojectiveKoszulDifferential k v n).hom
  | 0 => range_preprojectiveKoszulLeft_eq_ker_right k v
  | 1 => by
    simp only [preprojectiveKoszulDifferential, ModuleCat.hom_zero, LinearMap.range_zero]
    exact ((LinearMap.ker_eq_bot).2 (preprojectiveKoszulLeft_injective k hQ v)).symm
  | n + 2 => by
    ext x
    have hx : x = 0 := by
      -- The term in degree `n + 3` is the zero module.
      exact Subsingleton.elim x 0
    simp [preprojectiveKoszulDifferential, hx]

/-- The vertex module of a quiver without sinks has a projective resolution supported in
homological degrees zero, one and two, with the Koszul maps as differentials. This is a
resolution over the opposite algebra, hence of right preprojective modules. -/
noncomputable def preprojectiveKoszulProjectiveResolution
    (hQ : ∀ u : Q, ∃ w, Nonempty (u ⟶ w)) (v : Q) :
    ProjectiveResolution (ModuleCat.of Πᵐᵒᵖ (preprojectiveVertexModule k v)) where
  complex := preprojectiveKoszulComplex k v
  projective n := by
    rcases n with _ | (_ | (_ | n))
    · exact inferInstanceAs (Projective (ModuleCat.of Πᵐᵒᵖ
        (preprojectiveRightProjective k (Symmetrify.of.obj v))))
    · exact inferInstanceAs (Projective (ModuleCat.of Πᵐᵒᵖ (preprojectiveKoszulMiddle k v)))
    · exact inferInstanceAs (Projective (ModuleCat.of Πᵐᵒᵖ
        (preprojectiveRightProjective k (Symmetrify.of.obj v))))
    · exact (ModuleCat.isZero_of_subsingleton (ModuleCat.of Πᵐᵒᵖ PUnit)).projective
  «π» := preprojectiveKoszulComplexπ k v
  quasiIso := by
    constructor
    intro n
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros' _ rfl rfl rfl]
      refine ⟨?_, ?_⟩
      · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
        simp only [HomologicalComplex.shortComplexFunctor'_obj_f]
        exact (ker_preprojectiveVertexAugmentation k v).symm
      · rw [ModuleCat.epi_iff_surjective]
        exact preprojectiveVertexAugmentation_surjective k v
    | succ n =>
      rw [quasiIsoAt_iff_exactAt' (hL := ChainComplex.exactAt_succ_single_obj ..),
        HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp),
        ShortComplex.moduleCat_exact_iff_range_eq_ker]
      -- Identify the object instances carried by the short-complex wrapper with the
      -- explicit chain-complex terms before computing its differentials.
      change LinearMap.range (ChainComplex.of.d (preprojectiveKoszulTerm k v)
        (preprojectiveKoszulDifferential k v) (n + 1 + 1) (n + 1)).hom =
          LinearMap.ker (ChainComplex.of.d (preprojectiveKoszulTerm k v)
            (preprojectiveKoszulDifferential k v) (n + 1) n).hom
      rw [ChainComplex.of_d (preprojectiveKoszulTerm k v)
        (preprojectiveKoszulDifferential k v) (n + 1),
        ChainComplex.of_d (preprojectiveKoszulTerm k v) (preprojectiveKoszulDifferential k v) n]
      exact range_preprojectiveKoszulDifferential_succ_eq_ker k hQ v n

/-- The underlying complex of the projective resolution is the vertex Koszul complex. -/
@[simp]
theorem preprojectiveKoszulProjectiveResolution_complex
    (hQ : ∀ u : Q, ∃ w, Nonempty (u ⟶ w)) (v : Q) :
    (preprojectiveKoszulProjectiveResolution k hQ v).complex = preprojectiveKoszulComplex k v :=
  (rfl)

/-- The projectives of the resolution, identified with the explicit Koszul terms. -/
noncomputable def preprojectiveKoszulProjectiveResolutionXIso
    (hQ : ∀ u : Q, ∃ w, Nonempty (u ⟶ w)) (v : Q) (n : ℕ) :
    (preprojectiveKoszulProjectiveResolution k hQ v).complex.X n ≅ preprojectiveKoszulTerm k v n :=
  eqToIso (congrArg (fun C => C.X n) (preprojectiveKoszulProjectiveResolution_complex k hQ v)) ≪≫
    preprojectiveKoszulComplexXIso k v n

/-- The augmentation of the resolution is the vertex quotient map, using the explicit
identification of the zeroth Koszul term. -/
@[simp]
theorem preprojectiveKoszulProjectiveResolution_π_f_zero
    (hQ : ∀ u : Q, ∃ w, Nonempty (u ⟶ w)) (v : Q) :
    (preprojectiveKoszulProjectiveResolutionXIso k hQ v 0).inv ≫
        (preprojectiveKoszulProjectiveResolution k hQ v).π.f 0 =
      ModuleCat.ofHom (preprojectiveVertexAugmentation k v) := by
  -- Both term identifications are identities after expanding the constructed resolution.
  dsimp only [preprojectiveKoszulProjectiveResolutionXIso,
    preprojectiveKoszulProjectiveResolution, eqToIso_refl, Iso.trans_refl]
  exact preprojectiveKoszulComplexπ_f_zero k v

end TauCeti
