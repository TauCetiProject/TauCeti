/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.ValuedQuiver
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Jacobson.Semiprimary
import TauCeti.CategoryTheory.AlmostSplit.Minimal
import TauCeti.CategoryTheory.Linear.Conj

/-!
# A real–complex Auslander–Reiten mesh

For the real algebra of upper triangular matrices with real first and complex second diagonal
entry and complex upper corner, the two column modules give an almost-split sequence. The first
column embeds in the second by right multiplication by the upper matrix unit. The almost-split
sequence ends at the cokernel of this inclusion. Its middle term is indecomposable, so it occurs
with multiplicity one. The first arrow has real dimension two and valuation `(1, 2)`. The second
has valuation `(2, 1)`, and translation sends the cokernel vertex to the first-column vertex.

Open the scope `TauCeti.RealComplexTriangular` for the diagonal bimodule actions that implement
the algebra as a trivial square-zero extension.

Auslander, Reiten and Smalø give this example with the diagonal positions exchanged in
*Representation Theory of Artin Algebras*, §VII.2, p. 235. The multiplicity and valuation
comparison uses their Propositions VII.1.3 and VII.1.5.
-/

open CategoryTheory CategoryTheory.Limits MulOpposite
open scoped ModuleCat.Algebra

namespace TauCeti.RealComplexTriangular

noncomputable section

/-- The diagonal acts on the upper corner on the left through its real entry. -/
public scoped instance instModuleDiagonalComplex : Module (ℝ × ℂ) ℂ :=
  ((algebraMap ℝ ℂ).comp (RingHom.fst ℝ ℂ)).toModule

/-- The diagonal acts on the upper corner on the right through its complex entry. -/
public scoped instance instModuleDiagonalOppositeComplex : Module (ℝ × ℂ)ᵐᵒᵖ ℂ :=
  ((RingHom.snd ℝ ℂ).fromOpposite fun _ _ => Commute.all _ _).toModule

/-- Left real and right complex multiplication commute on the upper entry. -/
public scoped instance : SMulCommClass (ℝ × ℂ) (ℝ × ℂ)ᵐᵒᵖ ℂ where
  smul_comm a b x := mul_left_comm (a.1 : ℂ) (unop b).2 x

/-- Left multiplication on the upper entry is compatible with real scalar multiplication. -/
public scoped instance : IsScalarTower ℝ (ℝ × ℂ) ℂ where
  smul_assoc r a z := by
    -- The left diagonal action is through the real coordinate.
    change ((r * a.1 : ℝ) : ℂ) * z = r • ((a.1 : ℂ) * z)
    simp [Complex.real_smul, mul_assoc]

/-- Right multiplication on the upper entry is compatible with real scalar multiplication. -/
public scoped instance : IsScalarTower ℝ (ℝ × ℂ)ᵐᵒᵖ ℂ where
  smul_assoc r a z := by
    -- The right diagonal action is through the complex coordinate.
    change (r • (unop a).2) * z = r • ((unop a).2 * z)
    simp [Complex.real_smul, mul_assoc]

/-- The upper triangular real–complex algebra, written as diagonal and upper-corner coordinates. -/
public abbrev Triangular := TrivSqZeroExt (ℝ × ℂ) ℂ

local notation "T" => Triangular

private def entries (r : ℝ) (z s : ℂ) : T := ((r, s), z)

@[simp] private theorem entries_mul (r r' : ℝ) (z s z' s' : ℂ) :
    entries r z s * entries r' z' s' = entries (r * r') ((r : ℂ) * z' + s' * z) (s * s') :=
  rfl

@[simp] private theorem entries_fst (r : ℝ) (z s : ℂ) : (entries r z s).fst = (r, s) := rfl

@[simp] private theorem entries_snd (r : ℝ) (z s : ℂ) : (entries r z s).snd = z := rfl

@[simp] private theorem entries_add (r r' : ℝ) (z s z' s' : ℂ) :
    entries r z s + entries r' z' s' = entries (r + r') (z + z') (s + s') :=
  rfl

@[simp] private theorem algebraMap_entries (r : ℝ) :
    algebraMap ℝ T r = entries r 0 r := rfl

private def corner : T := entries 0 1 0

private def firstDiagonal : T →+* ℝ where
  toFun a := a.fst.1
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/-- The action of a triangular matrix on the real coordinate of its first column. -/
@[instance_reducible]
public def firstColumnModule : Module T ℝ := firstDiagonal.toModule

attribute [local instance] firstColumnModule

private def secondAction (a : T) (x : ℂ × ℂ) : ℂ × ℂ :=
  ((a.fst.1 : ℂ) * x.1 + a.snd * x.2, a.fst.2 * x.2)

-- Keep the bundled module's coordinate action ahead of the componentwise product action locally.
private instance (priority := high) : SMul T (ℂ × ℂ) := ⟨secondAction⟩

/-- The action of a triangular matrix on a second column with two complex coordinates. -/
@[instance_reducible]
public def secondColumnModule : Module T (ℂ × ℂ) where
  smul := secondAction
  -- The fields below explicitly compute the action being installed by this instance.
  one_smul x := show secondAction 1 x = x by simp [secondAction]
  mul_smul a b x := show secondAction (a * b) x = secondAction a (secondAction b x) by
    apply Prod.ext
    · simp only [secondAction, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, Prod.fst_mul]
      -- The two bimodule actions are multiplication by the respective diagonal entries.
      change ((a.fst.1 * b.fst.1 : ℝ) : ℂ) * x.1 +
        ((a.fst.1 : ℂ) * b.snd + b.fst.2 * a.snd) * x.2 =
          (a.fst.1 : ℂ) * ((b.fst.1 : ℂ) * x.1 + b.snd * x.2) + a.snd * (b.fst.2 * x.2)
      push_cast
      ring
    · exact mul_assoc _ _ _
  smul_zero a := show secondAction a 0 = 0 by simp [secondAction]
  smul_add a x y := show secondAction a (x + y) = secondAction a x + secondAction a y by
    apply Prod.ext <;> simp [secondAction] <;> ring
  add_smul a b x := show secondAction (a + b) x = secondAction a x + secondAction b x by
    apply Prod.ext <;> simp [secondAction] <;> ring
  zero_smul x := show secondAction 0 x = 0 by simp [secondAction]

attribute [local instance] secondColumnModule

/-- The first column of the real–complex triangular algebra. -/
public abbrev firstColumn : ModuleCat T := ModuleCat.of T ℝ

/-- The second column of the real–complex triangular algebra. -/
public abbrev secondColumn : ModuleCat T := ModuleCat.of T (ℂ × ℂ)

private theorem first_smul (a : T) (x : firstColumn) : a • x = a.fst.1 * x := rfl

private theorem second_smul (a : T) (x : secondColumn) :
    a • x = ((a.fst.1 : ℂ) * x.1 + a.snd * x.2, a.fst.2 * x.2) := rfl

private def inclusionLinear : ℝ →ₗ[T] (ℂ × ℂ) where
  toFun x := (x, 0)
  map_add' _ _ := by simp
  map_smul' a x := by
    -- Compute on the unbundled coordinate modules used to define this linear map.
    change (↑(a.fst.1 * x), 0) = secondAction a (↑x, 0)
    simp [secondAction]

/-- The upper matrix unit gives the map from the first column into the second column. -/
public def inclusion : firstColumn ⟶ secondColumn := ModuleCat.ofHom inclusionLinear

/-- The quotient sequence of the inclusion of the first column into the second column. -/
public noncomputable def sequence : ShortComplex (ModuleCat T) :=
  ShortComplex.mk inclusion (cokernel.π inclusion) (cokernel.condition inclusion)

/-- The first object of the sequence is the first column. -/
@[simp] public theorem sequence_X₁ : sequence.X₁ = firstColumn := (rfl)

/-- The middle object of the sequence is the second column. -/
@[simp] public theorem sequence_X₂ : sequence.X₂ = secondColumn := (rfl)

/-- The last object of the sequence is the cokernel of the inclusion. -/
@[simp] public theorem sequence_X₃ : sequence.X₃ = cokernel inclusion := (rfl)

/-- In column coordinates the first map is the inclusion. -/
@[simp] public theorem sequence_f :
    eqToHom sequence_X₁.symm ≫ sequence.f ≫ eqToHom sequence_X₂ = inclusion :=
  (by simp : 𝟙 firstColumn ≫ inclusion ≫ 𝟙 secondColumn = inclusion)

/-- In column coordinates the second map is the cokernel projection. -/
@[simp] public theorem sequence_g :
    eqToHom sequence_X₂.symm ≫ sequence.g ≫ eqToHom sequence_X₃ = cokernel.π inclusion :=
  (by simp : 𝟙 secondColumn ≫ cokernel.π inclusion ≫ 𝟙 _ = cokernel.π inclusion)

/-- On column coordinates, the first morphism embeds the real axis into the upper entry. -/
@[simp] public theorem inclusion_hom_apply (x : firstColumn) :
    inclusion.hom x = (((x : ℝ) : ℂ), 0) :=
  ModuleCat.ofHom_apply inclusionLinear x

private def e₁ : T := entries 1 0 0
private def e₂ : T := entries 0 0 1

private theorem firstColumn_toSpanSingleton_surjective :
    Function.Surjective (LinearMap.toSpanSingleton T firstColumn (1 : ℝ)) :=
  fun x => ⟨entries x 0 0, (first_smul _ _).trans (by simp)⟩

private theorem secondColumn_toSpanSingleton_surjective :
    Function.Surjective (LinearMap.toSpanSingleton T secondColumn ((0, 1) : ℂ × ℂ)) :=
  fun x => ⟨entries 0 x.1 x.2, (second_smul _ _).trans (by simp)⟩

private theorem firstColumn_ext {M : ModuleCat T} {f g : firstColumn ⟶ M}
    (h : f (1 : ℝ) = g (1 : ℝ)) : f = g :=
  ModuleCat.hom_ext ((LinearMap.cancel_right firstColumn_toSpanSingleton_surjective).mp
    (LinearMap.ext_ring (by simpa only [LinearMap.comp_apply,
      LinearMap.toSpanSingleton_apply_one] using h)))

private theorem secondColumn_ext {M : ModuleCat T} {f g : secondColumn ⟶ M}
    (h : f ((0, 1) : ℂ × ℂ) = g ((0, 1) : ℂ × ℂ)) : f = g :=
  ModuleCat.hom_ext ((LinearMap.cancel_right secondColumn_toSpanSingleton_surjective).mp
    (LinearMap.ext_ring (by simpa only [LinearMap.comp_apply,
      LinearMap.toSpanSingleton_apply_one] using h)))

private def fromSecond {M : ModuleCat T} (x : M) : secondColumn ⟶ M :=
  ModuleCat.ofHom
    { toFun := fun y => entries 0 y.1 y.2 • x
      map_add' := fun a b => by
        rw [← add_smul]
        congr 1
        simp
      map_smul' := fun a b => by
        rcases a with ⟨⟨r, s⟩, z⟩
        rw [← mul_smul]
        congr 1
        -- The source action is the second column of the product of two triangular matrices.
        change entries 0 (secondAction (entries r z s) b).1
          (secondAction (entries r z s) b).2 = entries r z s * entries 0 b.1 b.2
        rw [entries_mul]
        simp [secondAction, mul_comm] }

private theorem inclusion_fromSecond_apply {M : ModuleCat T} (x : M) :
    (inclusion ≫ fromSecond x) (1 : ℝ) = corner • x := by
  rfl

private theorem not_isSplitMono_inclusion : ¬ IsSplitMono inclusion := by
  intro h
  let r := retraction inclusion
  have hzero : corner • r ((0, 1) : ℂ × ℂ) = (0 : ℝ) :=
    (first_smul _ _).trans (by simp [corner])
  have hcol : corner • (((0, 1) : ℂ × ℂ) : secondColumn) = ((1, 0) : ℂ × ℂ) :=
    (second_smul _ _).trans (by simp [corner])
  have hr := ConcreteCategory.congr_hom (IsSplitMono.id (f := inclusion)) (1 : ℝ)
  have he : r ((1, 0) : ℂ × ℂ) = (1 : ℝ) := hr
  exact one_ne_zero (he.symm.trans (hcol ▸ (r.hom.map_smul corner _).trans hzero))

private def cornerAction (M : ModuleCat T) : Module.End ℝ M :=
  Algebra.lsmul ℝ ℝ M corner

private def toFirst {M : ModuleCat T} (φ : M →ₗ[ℝ] ℝ)
    (hφ : ∀ x : M, φ (corner • x) = 0) : M ⟶ firstColumn :=
  ModuleCat.ofHom
    { toFun := fun x => φ (e₁ • x)
      map_add' := fun x y => by rw [smul_add, map_add]
      map_smul' := fun a x => by
        rcases a with ⟨⟨r, s⟩, z⟩
        have hm : e₁ * entries r z s =
            algebraMap ℝ T r * e₁ + corner * entries 0 0 z := by
          simp [e₁, corner]
        -- The off-diagonal term belongs to the range annihilated by the functional.
        change φ (e₁ • entries r z s • x) = r * φ (e₁ • x)
        rw [← mul_smul, hm, add_smul, mul_smul, mul_smul, algebraMap_smul, map_add, hφ,
          add_zero, map_smul, smul_eq_mul] }

/-- The inclusion of the first column in the second is left almost split in the module category. -/
public theorem isLeftAlmostSplit_inclusion : IsLeftAlmostSplit inclusion := by
  refine isLeftAlmostSplit_iff.mpr ⟨not_isSplitMono_inclusion, fun M g hg => ?_⟩
  by_cases h : g (1 : ℝ) ∈ LinearMap.range (cornerAction M)
  · obtain ⟨x, hx⟩ := h
    exact ⟨fromSecond x, firstColumn_ext ((inclusion_fromSecond_apply x).trans hx)⟩
  · obtain ⟨φ, hn, hφ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem h inferInstance
    let ψ : M →ₗ[ℝ] ℝ := (φ (g (1 : ℝ)))⁻¹ • φ
    have hψ (x : M) : ψ (corner • x) = 0 := by
      have hz : φ (corner • x) = 0 := (Submodule.mem_bot ℝ).mp
        (hφ ▸ Submodule.mem_map_of_mem (f := φ) (LinearMap.mem_range_self (cornerAction M) x))
      exact mul_eq_zero_of_right _ hz
    have he : e₁ • g (1 : ℝ) = g (1 : ℝ) := by
      rw [← g.hom.map_smul]
      congr 1
      exact (first_smul e₁ (1 : ℝ)).trans (mul_one 1)
    have hsplit : g ≫ toFirst ψ hψ = 𝟙 _ := firstColumn_ext (by
      -- Evaluate the candidate retraction at the generator of the first column.
      change ψ (e₁ • g (1 : ℝ)) = 1
      rw [he]
      exact inv_mul_cancel₀ hn)
    exact (hg (IsSplitMono.mk' ⟨toFirst ψ hψ, hsplit⟩)).elim

private def scaleSecond (c : ℂ) : secondColumn ⟶ secondColumn :=
  ModuleCat.ofHom
    { toFun := fun x => (c * x.1, c * x.2)
      map_add' := fun x y => Prod.ext (mul_add c x.1 y.1) (mul_add c x.2 y.2)
      map_smul' := fun a x => by
        -- Coordinatewise complex multiplication commutes with the triangular action.
        change (c * (secondAction a x).1, c * (secondAction a x).2) =
          secondAction a (c * x.1, c * x.2)
        apply Prod.ext <;> dsimp [secondAction] <;> ring }

private theorem secondColumn_map_generator (f : secondColumn ⟶ secondColumn) :
    (f ((0, 1) : ℂ × ℂ)).1 = 0 := by
  have hfix : e₂ • (((0, 1) : ℂ × ℂ) : secondColumn) = ((0, 1) : ℂ × ℂ) :=
    (second_smul _ _).trans (by simp [e₂])
  have hf := congrArg Prod.fst (f.hom.map_smul e₂ (((0, 1) : ℂ × ℂ) : secondColumn))
  rw [hfix] at hf
  exact hf.trans (congrArg Prod.fst (second_smul _ _)) |>.trans (by simp [e₂])

private theorem scaleSecond_apply (c : ℂ) (x : secondColumn) :
    scaleSecond c x = (c * x.1, c * x.2) := rfl

private theorem scaleSecond_eq (f : secondColumn ⟶ secondColumn) :
    scaleSecond (f ((0, 1) : ℂ × ℂ)).2 = f := by
  apply secondColumn_ext
  rw [scaleSecond_apply, mul_zero, mul_one]
  exact Prod.ext (secondColumn_map_generator f).symm rfl

private theorem scaleSecond_generator (c : ℂ) : scaleSecond c ((0, 1) : ℂ × ℂ) = (0, c) :=
  (scaleSecond_apply _ _).trans (by simp)

private def scaleSecondAlgHom : ℂ →ₐ[ℝ] End secondColumn where
  toFun c := End.of (scaleSecond c)
  map_zero' := End.ext (secondColumn_ext (by
    rw [scaleSecond_generator]
    rfl))
  map_one' := End.ext (secondColumn_ext (by
    rw [scaleSecond_generator]
    rfl))
  map_add' c d := End.ext (secondColumn_ext (by
    -- Computing the sum at the column generator reduces it to the sum of the scalars.
    change scaleSecond (c + d) ((0, 1) : ℂ × ℂ) =
      scaleSecond c ((0, 1) : ℂ × ℂ) + scaleSecond d ((0, 1) : ℂ × ℂ)
    rw [scaleSecond_generator, scaleSecond_generator, scaleSecond_generator]
    exact Prod.ext (zero_add 0).symm rfl))
  map_mul' c d := End.ext (secondColumn_ext (by
    -- Multiplication in the endomorphism algebra is composition.
    change scaleSecond (c * d) ((0, 1) : ℂ × ℂ) =
      scaleSecond c (scaleSecond d ((0, 1) : ℂ × ℂ))
    rw [scaleSecond_generator, scaleSecond_generator, scaleSecond_apply, mul_zero]))
  commutes' r := End.ext (secondColumn_ext (by
    -- The real scalar acts through the two diagonal entries of the scalar matrix.
    change scaleSecond (r : ℂ) ((0, 1) : ℂ × ℂ) =
      algebraMap ℝ T r • (((0, 1) : ℂ × ℂ) : secondColumn)
    rw [scaleSecond_generator]
    exact ((second_smul _ _).trans (by simp)).symm))

/-- The endomorphism algebra of the second column is the complex field. -/
public def secondColumnEndEquiv : ℂ ≃ₐ[ℝ] End secondColumn :=
  AlgEquiv.ofBijective scaleSecondAlgHom
    ⟨fun c d h => by
      have h' := congrArg (fun f : End secondColumn => (f.asHom ((0, 1) : ℂ × ℂ)).2) h
      exact (congrArg Prod.snd (scaleSecond_generator c)).symm.trans
        (h'.trans (congrArg Prod.snd (scaleSecond_generator d))),
      fun f => ⟨(f.asHom ((0, 1) : ℂ × ℂ)).2, End.ext (scaleSecond_eq f.asHom)⟩⟩

/-- The endomorphism associated to a complex scalar multiplies both entries by that scalar. -/
@[simp] public theorem secondColumnEndEquiv_apply (c : ℂ) (x : secondColumn) :
    (secondColumnEndEquiv c).asHom x = (c * x.1, c * x.2) := (rfl)

private instance : IsLocalRing (End secondColumn) :=
  secondColumnEndEquiv.toRingEquiv.isLocalRing

private theorem mono_inclusion : Mono inclusion :=
  (ModuleCat.mono_iff_injective _).mpr (fun _ _ h => Complex.ofReal_injective (congrArg Prod.fst h))

/-- The sequence from the first column to the second and its cokernel is almost split. -/
public theorem isAlmostSplit_sequence : sequence.IsAlmostSplit := by
  have hS : sequence.ShortExact := by
    unfold sequence
    have := mono_inclusion
    exact { exact := ShortComplex.exact_cokernel inclusion }
  refine hS.isAlmostSplit_of_isLeftAlmostSplit isLeftAlmostSplit_inclusion (fun b hb => ?_)
  obtain ⟨c, hc⟩ := secondColumnEndEquiv.surjective (End.of b)
  have he : scaleSecond c = b := congrArg End.asHom hc
  have hc₁ : c = 1 := by
    rw [← he] at hb
    have ha := congrArg Prod.fst (ConcreteCategory.congr_hom hb (1 : ℝ))
    -- Evaluating the equality on the first column's generator gives the scalar itself.
    change (scaleSecond c ((1, 0) : ℂ × ℂ)).1 = 1 at ha
    rw [scaleSecond_apply] at ha
    exact (mul_one c).symm.trans ha
  have hb₁ : b = 𝟙 secondColumn := by
    rw [← he, hc₁]
    exact congrArg End.asHom secondColumnEndEquiv.map_one
  exact hb₁.symm ▸ inferInstanceAs (IsIso (𝟙 secondColumn))

private theorem algebraMap_firstColumn_generator (r : ℝ) :
    (algebraMap ℝ (End firstColumn) r).asHom (1 : ℝ) = r :=
  (first_smul (algebraMap ℝ T r) (1 : ℝ)).trans (by simp)

/-- The endomorphism algebra of the first column is the real field. -/
public def firstColumnEndEquiv : ℝ ≃ₐ[ℝ] End firstColumn :=
  AlgEquiv.ofBijective (Algebra.ofId ℝ (End firstColumn)) ⟨fun r s h =>
    (algebraMap_firstColumn_generator r).symm.trans
      ((congrArg (fun f : End firstColumn => f.asHom (1 : ℝ)) h).trans
        (algebraMap_firstColumn_generator s)), fun f =>
    ⟨f.asHom (1 : ℝ), End.ext (firstColumn_ext (algebraMap_firstColumn_generator _))⟩⟩

/-- The endomorphism associated to a real scalar acts by multiplication on the first column. -/
@[simp] public theorem firstColumnEndEquiv_apply (r : ℝ) (x : firstColumn) :
    (firstColumnEndEquiv r).asHom x = r * x :=
  (first_smul (algebraMap ℝ T r) x).trans (by simp)

private theorem finrank_residue_of_iso_firstColumn {X : ModuleCat T} (e : X ≅ firstColumn) :
    Module.finrank ℝ ((End X)ᵐᵒᵖ ⧸ Ring.jacobson (End X)ᵐᵒᵖ) = 1 := by
  let d := (e.conjAlgEquiv ℝ).trans firstColumnEndEquiv.symm
  have : IsSemisimpleRing (End X) := d.toRingEquiv.isSemisimpleRing_iff.mpr inferInstance
  rw [TauCeti.Ring.finrank_quotient_jacobson_mulOpposite]
  exact ((Submodule.quotEquivOfEqBot ((Ring.jacobson (End X)).restrictScalars ℝ)
    (by rw [IsSemisimpleRing.jacobson_eq_bot]; rfl)).trans d.toLinearEquiv).finrank_eq.trans
      (Module.finrank_self ℝ)

private theorem finrank_residue_of_iso_secondColumn {X : ModuleCat T} (e : X ≅ secondColumn) :
    Module.finrank ℝ (End X ⧸ Ring.jacobson (End X)) = 2 := by
  let d := (e.conjAlgEquiv ℝ).trans secondColumnEndEquiv.symm
  have : IsSemisimpleRing (End X) := d.toRingEquiv.isSemisimpleRing_iff.mpr inferInstance
  exact ((Submodule.quotEquivOfEqBot ((Ring.jacobson (End X)).restrictScalars ℝ)
    (by rw [IsSemisimpleRing.jacobson_eq_bot]; rfl)).trans d.toLinearEquiv).finrank_eq.trans
      Complex.finrank_real_complex

/-- The first arrow of the mesh has valuation `(1, 2)`. The first entry counts the copy of the
second column in the middle term of the almost-split sequence. -/
public theorem irreducibleMorphismValuation_firstColumn_secondColumn :
    irreducibleMorphismValuation ℝ firstColumn secondColumn = (1, 2) := by
  have : IsLocalRing (End firstColumn) := firstColumnEndEquiv.toRingEquiv.isLocalRing
  have ha : (irreducibleMorphismValuation ℝ firstColumn secondColumn).1 = 1 :=
    (isAlmostSplit_sequence.irreducibleMorphismValuation_fst_eq_finrank ℝ secondColumn).trans
      (finrank_residue_radicalQuotient_self ℝ secondColumn)
  have htarget := finrank_residue_mul_irreducibleMorphismValuation_fst ℝ firstColumn secondColumn
  have hsource := finrank_residueOp_mul_irreducibleMorphismValuation_snd ℝ firstColumn secondColumn
  rw [finrank_residue_of_iso_secondColumn (Iso.refl _), ha, mul_one] at htarget
  rw [finrank_residue_of_iso_firstColumn (Iso.refl _), one_mul, ← htarget] at hsource
  exact Prod.ext ha hsource

/-- The space of irreducible maps from the first column to the second has real dimension two. -/
public theorem finrank_irreducibleMorphismSpace_firstColumn_secondColumn :
    Module.finrank ℝ (irreducibleMorphismSpace ℝ firstColumn secondColumn) = 2 := by
  rw [← finrank_residue_mul_irreducibleMorphismValuation_fst,
    finrank_residue_of_iso_secondColumn (Iso.refl _),
    irreducibleMorphismValuation_firstColumn_secondColumn]
  rfl

/-- The triangular algebra has finite real dimension. -/
public instance : Module.Finite ℝ T :=
  Module.Finite.equiv
    (LinearEquiv.refl ℝ ((ℝ × ℂ) × ℂ) : ((ℝ × ℂ) × ℂ) ≃ₗ[ℝ] T)

private instance : Module.Finite T firstColumn :=
  Module.Finite.of_surjective _ firstColumn_toSpanSingleton_surjective

private instance : Module.Finite T secondColumn :=
  Module.Finite.of_surjective _ secondColumn_toSpanSingleton_surjective

private instance : Module.Finite T sequence.X₃ :=
  Module.Finite.of_surjective (cokernel.π inclusion).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

/-- The second arrow of the same mesh has valuation `(2, 1)`. Its second entry
counts the same middle summand as the first entry of the incoming map to the middle term. -/
public theorem irreducibleMorphismValuation_secondColumn_cokernel :
    irreducibleMorphismValuation ℝ secondColumn sequence.X₃ = (2, 1) := by
  have : Module.Finite ℝ (End sequence.X₃) := Module.Finite.equiv End.linearEquiv.symm
  have h := isAlmostSplit_sequence.irreducibleMorphismValuation_X₁_eq_swap ℝ
    (fun _ : Unit => secondColumn) (biproductUniqueIso (fun _ : Unit => secondColumn)).symm
    secondColumn
  rw [← Prod.swap_swap (irreducibleMorphismValuation ℝ secondColumn sequence.X₃), ← h,
    sequence_X₁, irreducibleMorphismValuation_firstColumn_secondColumn]
  rfl

/-- The isomorphism classes of finite indecomposable modules of the real–complex algebra. -/
public abbrev Vertex :=
  IrreducibleMorphismQuiver ℝ (fun M : ModuleCat T => Module.Finite T M)

private theorem indecomposable_secondColumn : Indecomposable secondColumn :=
  indecomposable_of_isLocalRing_end

/-- The vertex represented by the first column. -/
public def firstVertex : Vertex :=
  IrreducibleMorphismQuiver.of ℝ (P := fun M : ModuleCat T => Module.Finite T M)
    (M := firstColumn) inferInstance isLeftAlmostSplit_inclusion.indecomposable

/-- The vertex represented by the second column. -/
public def secondVertex : Vertex :=
  IrreducibleMorphismQuiver.of ℝ (P := fun M : ModuleCat T => Module.Finite T M)
    (M := secondColumn) inferInstance indecomposable_secondColumn

/-- The vertex represented by the cokernel of the inclusion of the columns. -/
public def cokernelVertex : Vertex :=
  IrreducibleMorphismQuiver.of ℝ (P := fun M : ModuleCat T => Module.Finite T M)
    (M := sequence.X₃) inferInstance isAlmostSplit_sequence.isRightAlmostSplit_g.indecomposable

/-- The translation sends the cokernel vertex to the first column vertex. -/
public theorem translate_cokernelVertex :
    (ModuleCat.arTranslation ℝ T ℝ (length_quotient_linearMap_self_eq_one (R := ℝ))).translate
      cokernelVertex = some firstVertex := by
  have hI := isAlmostSplit_sequence.isRightAlmostSplit_g.indecomposable
  have := isAlmostSplit_sequence.shortExact.epi_g
  have hp := isAlmostSplit_sequence.isRightAlmostSplit_g.not_projective
  let hE := length_quotient_linearMap_self_eq_one ℝ
  obtain ⟨_, _, _, _, _, hS⟩ := ModuleCat.exists_isAlmostSplit_arTranslate ℝ ℝ hE sequence.X₃ hI hp
  have hi := hS.nonempty_iso_X₁ isAlmostSplit_sequence (Iso.refl sequence.X₃)
  unfold cokernelVertex firstVertex
  refine ((ModuleCat.arTranslation ℝ T ℝ hE).translate_of_eq_some_of_iff (k := ℝ) _ hI _
    isLeftAlmostSplit_inclusion.indecomposable).2 ⟨hp, ?_⟩
  rw [ModuleCat.arTranslation_obj]
  exact hi.map fun e => e ≪≫ eqToIso sequence_X₁

/-- The first arrow in the valued Auslander–Reiten quiver has label `(1, 2)`. -/
public theorem valuationMatrix_firstVertex_secondVertex :
    IrreducibleMorphismQuiver.valuationMatrix ℝ _ firstVertex secondVertex = some (1, 2) := by
  let e₁' : firstVertex.representative ≅ firstColumn :=
    IrreducibleMorphismQuiver.representativeIso ℝ (P := fun M : ModuleCat T => Module.Finite T M)
      (M := firstColumn) inferInstance isLeftAlmostSplit_inclusion.indecomposable
  let e₂' : secondVertex.representative ≅ secondColumn :=
    IrreducibleMorphismQuiver.representativeIso ℝ (P := fun M : ModuleCat T => Module.Finite T M)
      (M := secondColumn) inferInstance indecomposable_secondColumn
  apply IrreducibleMorphismQuiver.valuationMatrix_eq_some_iff.mpr
  have h := (irreducibleMorphismSpaceCongr ℝ e₁' e₂').finrank_eq.trans
    finrank_irreducibleMorphismSpace_firstColumn_secondColumn
  have ha := finrank_residue_mul_irreducibleMorphismValuation_fst ℝ
    firstVertex.representative secondVertex.representative
  have hb := finrank_residueOp_mul_irreducibleMorphismValuation_snd ℝ
    firstVertex.representative secondVertex.representative
  rw [finrank_residue_of_iso_secondColumn e₂', h] at ha
  rw [finrank_residue_of_iso_firstColumn e₁', one_mul, h] at hb
  exact Prod.ext (Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) ha) hb

/-- The translated arrow in the valued Auslander–Reiten quiver has label `(2, 1)`. -/
public theorem valuationMatrix_secondVertex_cokernelVertex :
    IrreducibleMorphismQuiver.valuationMatrix ℝ _ secondVertex cokernelVertex = some (2, 1) := by
  have h := IrreducibleMorphismQuiver.valuationMatrix_eq_map_swap
    (ModuleCat.irreducibleMorphismValuation_eq_swap_of_translate_eq_some
      translate_cokernelVertex secondVertex)
  rw [valuationMatrix_firstVertex_secondVertex] at h
  simpa using (congrArg (Option.map Prod.swap) h).symm

end

end TauCeti.RealComplexTriangular
