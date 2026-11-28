/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Length
public import TauCeti.Algebra.Category.FGModuleCat.Basic
public import TauCeti.CategoryTheory.Preadditive.Radical.Basic
public import TauCeti.RepresentationTheory.Quiver.Kronecker.PathAlgebra
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.RingTheory.HopkinsLevitzki
import TauCeti.Algebra.Category.FGModuleCat.KrullSchmidt
import TauCeti.Algebra.Category.ModuleCat.Length
import TauCeti.CategoryTheory.Abelian.Length
import TauCeti.RepresentationTheory.Quiver.Acyclic.PathAlgebra
import TauCeti.RepresentationTheory.Quiver.Kronecker.FiniteRepType
import TauCeti.RepresentationTheory.Quiver.Representation.FiniteDimensional

/-!
# Unbounded length and infinite radical for Kronecker algebras

For the path algebra of a generalized Kronecker quiver with a finite set of at least two arrows,
the Jordan blocks give finitely generated indecomposable modules of unbounded composition
length. The quotients between consecutive blocks give factorizations of one fixed nonzero
morphism through arbitrarily many radical maps. It starts at the simple at the sink and takes its
generator to the unit vector at the sink of the smallest Jordan block.

The two-arrow case is the Kronecker algebra. See Auslander, Reiten and Smalø,
*Representation Theory of Artin Algebras*, §VIII.7, pp. 302–305, for the path-algebra description
and the regular family over an algebraically closed field. Here the chosen Jordan blocks and
their quotient maps work over any field.
-/

public section

namespace TauCeti

open CategoryTheory Polynomial
open Quiver.Kronecker

universe u v

variable {k : Type u} [Field k] {A : Type v}

private abbrev jordanSpace (k : Type u) [Field k] (n : ℕ) :=
  AdjoinRoot ((X : k[X]) ^ (n + 1))

private noncomputable def jordanQuotient (n : ℕ) : jordanSpace k (n + 1) →ₐ[k] jordanSpace k n :=
  Ideal.Quotient.factorₐ k (Ideal.span_singleton_le_span_singleton.mpr
    (pow_dvd_pow (X : k[X]) (Nat.le_succ (n + 1))))

private theorem jordanQuotient_surjective (n : ℕ) :
    Function.Surjective (jordanQuotient (k := k) n) := by
  intro y
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective y
  exact ⟨AdjoinRoot.mk _ p, Ideal.Quotient.factorₐ_apply_mk _ _ _⟩

private noncomputable def jordanRepQuotient (a : A) (n : ℕ) :
    kroneckerJordanRep k a (n + 1) ⟶ kroneckerJordanRep k a n :=
  kroneckerHom (ModuleCat.ofHom (jordanQuotient n).toLinearMap)
    (ModuleCat.ofHom (jordanQuotient n).toLinearMap) fun b ↦ by
      by_cases h : b = a
      · subst b
        rw [kroneckerJordanRep_map_arrowPath_self, kroneckerJordanRep_map_arrowPath_self]
        refine ModuleCat.hom_ext (LinearMap.ext fun (x : jordanSpace k (n + 1)) ↦ ?_)
        -- Read the two bundled composites on the quotient-ring carriers.
        change jordanQuotient n (AdjoinRoot.root ((X : k[X]) ^ (n + 1 + 1)) * x) =
          AdjoinRoot.root ((X : k[X]) ^ (n + 1)) * jordanQuotient n x
        rw [map_mul]
        exact congrArg (· * jordanQuotient n x) (Ideal.Quotient.factorₐ_apply_mk k _ X)
      · rw [kroneckerJordanRep_map_arrowPath_of_ne h, kroneckerJordanRep_map_arrowPath_of_ne h]
        exact (Category.id_comp _).trans (Category.comp_id _).symm

private theorem epi_jordanRepQuotient (a : A) (n : ℕ) :
    Epi (jordanRepQuotient (k := k) a n) := by
  rw [NatTrans.epi_iff_epi_app]
  intro i
  have hq : Epi (ModuleCat.ofHom (jordanQuotient (k := k) n).toLinearMap) :=
    (ModuleCat.epi_iff_surjective _).mpr (jordanQuotient_surjective n)
  cases i with
  | src =>
    have h : (jordanRepQuotient (k := k) a n).app (src : Paths (Quiver.Kronecker A)) =
        ModuleCat.ofHom (jordanQuotient n).toLinearMap := kroneckerHom_app_src _ _ _
    exact h.symm ▸ hq
  | tgt =>
    have h : (jordanRepQuotient (k := k) a n).app (tgt : Paths (Quiver.Kronecker A)) =
        ModuleCat.ofHom (jordanQuotient n).toLinearMap := kroneckerHom_app_tgt _ _ _
    exact h.symm ▸ hq

private theorem not_isIso_jordanRepQuotient (a : A) (n : ℕ) :
    ¬ IsIso (jordanRepQuotient (k := k) a n) := fun _ ↦
  Nat.succ_ne_self n
    (eq_of_nonempty_kroneckerJordanRep_iso ⟨asIso (jordanRepQuotient (k := k) a n)⟩)

private theorem jordanUnit_map_eq_zero (a : A) (n : ℕ)
    {j : Quiver.Kronecker A} (p : Quiver.Path tgt j) (hp : p.length ≠ 0) :
    (kroneckerJordanRep k a n).map p (1 : jordanSpace k n) = 0 := by
  obtain rfl := isSink_tgt.eq_of_path p
  exact (hp (by simp [path_tgt_tgt_eq_nil p])).elim

private noncomputable def simpleToJordan (a : A) (n : ℕ) :
    simpleRep k (Quiver.Kronecker A) tgt ⟶ kroneckerJordanRep k a n :=
  simpleRepHom (1 : jordanSpace k n) (jordanUnit_map_eq_zero a n)

private theorem simpleToJordan_app_generator (a : A) (n : ℕ) :
    (simpleToJordan (k := k) a n).app ((Paths.of (Quiver.Kronecker A)).obj tgt)
      (simpleRepGenerator k (tgt : Quiver.Kronecker A)) = (1 : jordanSpace k n) :=
  simpleRepHom_app_generator _ (jordanUnit_map_eq_zero a n)

private theorem simpleToJordan_comp (a : A) (n : ℕ) :
    simpleToJordan (k := k) a (n + 1) ≫ jordanRepQuotient a n = simpleToJordan a n := by
  refine kroneckerRep_hom_ext (Limits.IsZero.eq_of_src (isZero_simpleRep_obj src_ne_tgt) _ _) ?_
  -- Use the vertex as an object of the path category to rewrite the natural transformations.
  let i := (Paths.of (Quiver.Kronecker A)).obj (tgt : Quiver.Kronecker A)
  change (simpleToJordan a (n + 1) ≫ jordanRepQuotient a n).app i = (simpleToJordan a n).app i
  rw [NatTrans.comp_app]
  have hq : (jordanRepQuotient (k := k) a n).app i =
      ModuleCat.ofHom (jordanQuotient n).toLinearMap := kroneckerHom_app_tgt _ _ _
  refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  obtain ⟨c, rfl⟩ := exists_eq_smul_simpleRepGenerator k x
  -- Evaluate the two linear maps on a scalar multiple of the sink generator.
  change ((simpleToJordan a (n + 1)).app i ≫ (jordanRepQuotient a n).app i)
      (c • simpleRepGenerator k (tgt : Quiver.Kronecker A)) =
    (simpleToJordan a n).app i (c • simpleRepGenerator k (tgt : Quiver.Kronecker A))
  rw [hq]
  simp only [map_smul]
  -- The second map in the composite is the quotient algebra homomorphism.
  let generator := simpleRepGenerator k (tgt : Quiver.Kronecker A)
  change c • jordanQuotient n ((simpleToJordan a (n + 1)).app i generator) =
    c • (simpleToJordan a n).app i generator
  exact congrArg (c • ·) (by
    dsimp only [i, generator]
    rw [simpleToJordan_app_generator, simpleToJordan_app_generator, map_one])

private theorem simpleToJordan_ne_zero (a : A) (n : ℕ) :
    simpleToJordan (k := k) a n ≠ 0 := by
  intro h
  have hn : (simpleToJordan (k := k) a n).app ((Paths.of (Quiver.Kronecker A)).obj tgt) = 0 :=
    (simpleRep_hom_eq_zero_iff _).mp h
  apply one_ne_zero (α := jordanSpace k n)
  rw [← simpleToJordan_app_generator (k := k) a n, hn]
  rfl

private noncomputable abbrev finiteRepToModule (k : Type u) [Field k] (A : Type v) :
    ObjectProperty.FullSubcategory (IsFinDim.{u, 0, v, u} k (Quiver.Kronecker A)) ⥤
      FGModuleCat.{u} (pathAlgebra k (Quiver.Kronecker A)) :=
  (ModuleCat.isFG _).lift (ObjectProperty.ι _ ⋙ (quiverRepEquivalence k _).functor)
    fun M ↦ (ModuleCat.isFG_iff _).mpr
      (module_finite_pathAlgebra_quiverRepEquivalenceFunctorObj_of_isFinDim k _ M.obj M.property)

private noncomputable abbrev finiteJordanRep (a : A) (n : ℕ) :
    ObjectProperty.FullSubcategory (IsFinDim.{u, 0, v, u} k (Quiver.Kronecker A)) :=
  ⟨kroneckerJordanRep k a n, isFinDim_kroneckerJordanRep⟩

private noncomputable abbrev finiteSinkSimple (k : Type u) [Field k] (A : Type v) :
    ObjectProperty.FullSubcategory (IsFinDim.{u, 0, v, u} k (Quiver.Kronecker A)) :=
  ⟨simpleRep k (Quiver.Kronecker A) tgt, isFinDim_iff.mpr fun i ↦
    finiteDimensional_simpleRep_obj (k := k) (tgt : Quiver.Kronecker A) i⟩

private theorem indecomposable_jordanModule {a b : A} (h : b ≠ a) (n : ℕ) :
    Indecomposable ((finiteRepToModule k A).obj (finiteJordanRep a n)).obj := by
  let e := quiverRepEquivalence.{u, 0, v, u} k (Quiver.Kronecker A)
  exact e.functor.indecomposable_obj_of_map_bijective
    (indecomposable_kroneckerJordanRep h) (e.fullyFaithfulFunctor.map_bijective _ _)

local instance [Finite A] : Finite (Quiver.TotalPath (Quiver.Kronecker A)) :=
  Finite.of_equiv (A ⊕ Bool) totalPathEquivArrowSumBool.symm

private theorem jordanModuleQuotient_mem_radical [Finite A] {a b : A} (h : b ≠ a) (n : ℕ) :
    (finiteRepToModule k A).map
      (ObjectProperty.homMk (X := finiteJordanRep a (n + 1)) (Y := finiteJordanRep a n)
        (jordanRepQuotient a n)) ∈
      (jacobsonRadicalIdeal (FGModuleCat.{u} (pathAlgebra k (Quiver.Kronecker A)))).hom _ _ := by
  have hlocal (m : ℕ) :
      IsLocalRing (End ((finiteRepToModule k A).obj (finiteJordanRep a m))) := by
    have := ((finiteRepToModule k A).obj (finiteJordanRep a m)).property
    exact FGModuleCat.isLocalRing_end_of_indecomposable (indecomposable_jordanModule h m)
  have := hlocal n
  have := hlocal (n + 1)
  let F := finiteRepToModule k A
  rw [jacobsonRadicalIdeal_hom, mem_jacobsonRadical_iff_not_isIso]
  intro hf
  let q : finiteJordanRep (k := k) a (n + 1) ⟶ finiteJordanRep a n :=
    ObjectProperty.homMk (jordanRepQuotient a n)
  have : IsIso q := isIso_of_fully_faithful F q
  exact not_isIso_jordanRepQuotient (k := k) a n ((ObjectProperty.isIso_hom_iff q).mpr this)

/-- The finitely generated indecomposable modules of a generalized Kronecker algebra
with at least two arrows have unbounded composition length. -/
theorem exists_lt_length_indecomposable_kronecker [Finite A] [Nontrivial A] (b : ℕ) :
    ∃ M : FGModuleCat.{u} (pathAlgebra k (Quiver.Kronecker A)),
      Indecomposable M ∧ (b : ℕ∞) < Module.length (pathAlgebra k (Quiver.Kronecker A)) M.obj := by
  obtain ⟨c, a, hca⟩ := exists_pair_ne A
  let e := quiverRepEquivalence.{u, 0, v, u} k (Quiver.Kronecker A)
  let M (n : ℕ) := (finiteRepToModule k A).obj (finiteJordanRep a n)
  -- A proper quotient of a module of finite length has strictly smaller length.
  have hlen (n : ℕ) : (n : ℕ∞) ≤ CategoryTheory.length (M n).obj := by
    induction n with
    | zero => simp
    | succ n ih =>
      let f : (M (n + 1)).obj ⟶ (M n).obj := e.functor.map (jordanRepQuotient a n)
      have := epi_jordanRepQuotient (k := k) a n
      have : Epi f := Functor.map_epi _ _
      have hlt : CategoryTheory.length (M n).obj < CategoryTheory.length (M (n + 1)).obj :=
        lt_of_le_of_ne (length_le_of_epi f) fun heq ↦ by
          have hfin : CategoryTheory.length (M n).obj ≠ ⊤ := by
            rw [ModuleCat.length_eq, Module.length_ne_top_iff]
            have := (M n).property
            exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
          have : IsIso (e.functor.map (jordanRepQuotient a n)) :=
            isIso_of_epi_of_length_eq f heq.symm hfin
          exact not_isIso_jordanRepQuotient a n (isIso_of_fully_faithful e.functor _)
      simpa only [Nat.cast_succ] using Order.add_one_le_of_lt (ih.trans_lt hlt)
  refine ⟨M (b + 1), (FGModuleCat.indecomposable_obj_iff _).mp
    (indecomposable_jordanModule hca _), ?_⟩
  rw [← ModuleCat.length_eq]
  exact (Nat.cast_lt.mpr (Nat.lt_succ_self _)).trans_le (hlen _)

/-- In the category of finitely generated modules of a generalized Kronecker algebra with at
least two arrows, there is a nonzero morphism between indecomposables in every radical power.
It is represented by the map from the simple at the sink sending its generator to the unit of
the size-one Jordan block. -/
theorem exists_ne_zero_mem_all_jacobsonRadicalIdeal_pow_kronecker [Finite A] [Nontrivial A] :
    ∃ (M N : FGModuleCat.{u} (pathAlgebra k (Quiver.Kronecker A))) (f : M ⟶ N),
      Indecomposable M ∧ Indecomposable N ∧ f ≠ 0 ∧
      ∀ n : ℕ, f ∈ (jacobsonRadicalIdeal _ ^ n).hom M N := by
  obtain ⟨c, a, hca⟩ := exists_pair_ne A
  let F := finiteRepToModule k A
  let S := F.obj (finiteSinkSimple k A)
  let M (n : ℕ) := F.obj (finiteJordanRep a n)
  let f (n : ℕ) : S ⟶ M n :=
    F.map (ObjectProperty.homMk (simpleToJordan a n))
  let e := quiverRepEquivalence.{u, 0, v, u} k (Quiver.Kronecker A)
  have hS : Indecomposable S := (FGModuleCat.indecomposable_obj_iff _).mp
    (e.functor.indecomposable_obj_of_map_bijective
      (indecomposable_of_simple (simpleRep k (Quiver.Kronecker A) tgt))
      (e.fullyFaithfulFunctor.map_bijective _ _))
  have hf : f 0 ≠ 0 := by
    intro hz
    apply simpleToJordan_ne_zero (k := k) a 0
    have hzero : (ObjectProperty.homMk (simpleToJordan a 0) :
        finiteSinkSimple k A ⟶ finiteJordanRep a 0) = 0 :=
      F.map_injective (by simpa only [Functor.map_zero] using hz)
    exact (congrArg (fun g : finiteSinkSimple k A ⟶ finiteJordanRep a 0 ↦ g.hom) hzero).trans
      (ObjectProperty.zero_hom _ _ _)
  refine ⟨S, M 0, f 0, hS, (FGModuleCat.indecomposable_obj_iff _).mp
    (indecomposable_jordanModule hca 0), hf, fun n ↦ ?_⟩
  -- Starting with a larger block gives one more radical factor at each step.
  suffices ∀ m, f m ∈ (jacobsonRadicalIdeal _ ^ n).hom S (M m) from this 0
  induction n with
  | zero => intro m; simp
  | succ n ih =>
    intro m
    let q : M (m + 1) ⟶ M m := F.map (ObjectProperty.homMk (jordanRepQuotient a m))
    have hcomp : f (m + 1) ≫ q = f m := by
      rw [← F.map_comp]
      exact congrArg F.map (ObjectProperty.hom_ext _ (simpleToJordan_comp a m))
    rw [← hcomp, pow_succ']
    exact MorphismIdeal.comp_mem_mul (ih (m + 1)) (jordanModuleQuotient_mem_radical hca m)

/-- No power of the radical of the finitely generated module category of a generalized Kronecker
algebra with at least two arrows is zero. -/
theorem jacobsonRadicalIdeal_pow_ne_bot_kronecker [Finite A] [Nontrivial A] (n : ℕ) :
    jacobsonRadicalIdeal (FGModuleCat.{u} (pathAlgebra k (Quiver.Kronecker A))) ^ n ≠ ⊥ := by
  obtain ⟨M, N, f, -, -, hf, h⟩ :=
    exists_ne_zero_mem_all_jacobsonRadicalIdeal_pow_kronecker (k := k) (A := A)
  intro hbot
  exact hf (by simpa [hbot] using h n)

end TauCeti
