/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Nikulin.Generator
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Primary.Decomposition
import Mathlib.Data.Nat.Factorization.Basic
import TauCeti.LinearAlgebra.FiniteBilinearModule.Decomposition
import TauCeti.LinearAlgebra.FiniteBilinearModule.Dyadic.Relations
import TauCeti.LinearAlgebra.FiniteBilinearModule.Dyadic.TwoElementary

/-!
# Nikulin decompositions, primary generator ranks, and dyadic cyclic summands

This file packages Nikulin's generator decomposition of a nondegenerate finite quadratic module `A`
into the bundled datum `TauCeti.FiniteQuadraticModule.NikulinDecomposition A`: a finite list of
admissible `NikulinGenerator` labels together with an explicit quadratic isometry onto their
orthogonal sum.

Although the list of generator labels is not unique — for instance, `u^{(2)}(2) ⊥ u^{(2)}(2)` and
`v^{(2)}(2) ⊥ v^{(2)}(2)` are isometric via `dyadicUProdSelfIsometryDyadicVProdSelf` — filtering a
decomposition to a prime `p` produces a `NikulinDecomposition` of the `p`-primary component
`A.primaryComponent p` from which intrinsic and lattice-realization invariants can be read off:

* the group cardinality `Nat.card A` and Gauss-sum invariant `A.gaussSign`;
* the `p`-primary additive generator rank `AddGroup.rank (A.primaryComponent p)` (`l(A_{q_p})` in
  Nikulin's notation), equal to the sum of `NikulinGenerator.rank` (`1` or `2`) over the
  `p`-primary labels in the decomposition, and hence the global generator rank `AddGroup.rank A`;
* the product `NikulinDecomposition.realizationDetProd` of the minimal `p`-adic realization
  determinants at prime `p`, whose `p`-part has absolute value `Nat.card (A.primaryComponent p)`;
* the dyadic boundary predicate `TauCeti.FiniteQuadraticModule.HasCyclicTwoSummand`, asserting an
  orthogonal summand `q_θ^{(2)}(2)` (`θ` odd), its invariance under passing to
  `A.primaryComponent 2`, and its characterization on nondegenerate `2`-elementary modules as the
  failure of `q` to take values in `½ℤ/ℤ`.

## Main definitions

* `TauCeti.FiniteQuadraticModule.NikulinDecomposition`: a list of admissible `NikulinGenerator`s
  together with an isometry `A.Isometry (orthogonalSumNikulinGenerators generators)`.
* `TauCeti.FiniteQuadraticModule.NikulinDecomposition.ofIsNondegenerate`: builds a
  `NikulinDecomposition` for any nondegenerate finite quadratic module from
  `exists_isometry_prod_pi_generators`.
* `TauCeti.FiniteQuadraticModule.NikulinDecomposition.primaryComponent`: filters a decomposition of
  `A` to a decomposition of `A.primaryComponent p` for a prime `p`.
* `TauCeti.FiniteQuadraticModule.NikulinDecomposition.realizationDetProd`: product of
  `NikulinGenerator.realizationDet` over the `p`-primary generators of a decomposition.
* `TauCeti.FiniteQuadraticModule.HasCyclicTwoSummand`: existence of an orthogonal summand
  `dyadicCyclic 1 θ` with `θ` odd.

## Main results

* `TauCeti.FiniteQuadraticModule.nonempty_nikulinDecomposition_iff`: `NikulinDecomposition A` is
  nonempty if and only if `A` is nondegenerate.
* `TauCeti.FiniteQuadraticModule.NikulinDecomposition.rank_primaryComponent_eq` and
  `TauCeti.FiniteQuadraticModule.NikulinDecomposition.rank_eq`: express `AddGroup.rank` on
  `A.primaryComponent p` and on `A` in terms of `NikulinGenerator.rank`.
* `TauCeti.FiniteQuadraticModule.NikulinDecomposition.ordProj_natAbs_realizationDetProd`: the
  `p`-part of `|D.realizationDetProd p|` equals `Nat.card (A.primaryComponent p)`.
* `TauCeti.FiniteQuadraticModule.hasCyclicTwoSummand_primaryComponent_two_iff`: for nondegenerate
  `A`, `A.primaryComponent 2` has a cyclic order-two summand if and only if `A` does.
* `TauCeti.FiniteQuadraticModule.hasCyclicTwoSummand_iff_of_two_nsmul_eq_zero`: on a nondegenerate
  `2`-elementary module, `HasCyclicTwoSummand A` holds if and only if `q` does not take all its
  values in `½ℤ/ℤ`.
* `TauCeti.FiniteQuadraticModule.exists_ne_generators_nikulinDecomposition`: `NikulinDecomposition`
  labels are not unique on `(dyadicU 1).prod (dyadicU 1)`.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*,
  Propositions 1.8.1 and 1.8.2, Theorems 1.9.1 and 1.10.1, and §3.6.
* C. T. C. Wall, *Quadratic forms on finite groups, and related topics*, Topology 2 (1963),
  281–298.
-/

public section

namespace TauCeti.FiniteQuadraticModule

universe u v

/-! ## Bundled generator decompositions -/

/-- **A Nikulin generator decomposition** of a finite quadratic module `A`: a list of admissible
generator labels together with an isometry from `A` onto their orthogonal sum. -/
structure NikulinDecomposition (A : FiniteQuadraticModule.{u}) : Type u where
  /-- The generator labels in the orthogonal decomposition. -/
  generators : List NikulinGenerator
  /-- Every generator label in the list is admissible (positive exponent and unit parameter). -/
  admissible : ∀ g ∈ generators, g.IsAdmissible
  /-- The quadratic isometry identifying `A` with the orthogonal sum of `generators`. -/
  isometry : A.Isometry (orthogonalSumNikulinGenerators generators)

namespace NikulinDecomposition

/-- The empty generator decomposition of a trivial finite quadratic module. -/
noncomputable def empty (A : FiniteQuadraticModule.{u}) [Subsingleton A] :
    NikulinDecomposition A where
  generators := []
  admissible _ hg := nomatch hg
  isometry := Isometry.ofSubsingleton

@[simp]
theorem generators_empty (A : FiniteQuadraticModule.{u}) [Subsingleton A] :
    (empty A).generators = [] := (rfl)

/-- The one-element generator decomposition of an admissible generator's module. -/
noncomputable def singleton {g : NikulinGenerator} (hg : g.IsAdmissible) :
    NikulinDecomposition g.toFiniteQuadraticModule where
  generators := [g]
  admissible _ hmem := by
    rcases List.mem_singleton.mp hmem with rfl
    exact hg
  isometry := (orthogonalSumNikulinGeneratorsSingletonIsometry g).symm

@[simp]
theorem generators_singleton {g : NikulinGenerator} (hg : g.IsAdmissible) :
    (singleton hg).generators = [g] := (rfl)

/-- Transport a `NikulinDecomposition` along an isometry `A.Isometry B`. -/
noncomputable def ofIsometry {A : FiniteQuadraticModule.{u}} {B : FiniteQuadraticModule.{v}}
    (f : A.Isometry B) (D : NikulinDecomposition B) : NikulinDecomposition A where
  generators := D.generators
  admissible := D.admissible
  isometry := f.trans D.isometry

@[simp]
theorem generators_ofIsometry {A : FiniteQuadraticModule.{u}} {B : FiniteQuadraticModule.{v}}
    (f : A.Isometry B) (D : NikulinDecomposition B) :
    (D.ofIsometry f).generators = D.generators := (rfl)

/-- Concatenate decompositions of `A` and `B` into a decomposition of `A.prod B`. -/
noncomputable def prod {A : FiniteQuadraticModule.{u}} {B : FiniteQuadraticModule.{v}}
    (DA : NikulinDecomposition A) (DB : NikulinDecomposition B) :
    NikulinDecomposition (A.prod B) where
  generators := DA.generators ++ DB.generators
  admissible g hg := by
    rcases List.mem_append.mp hg with hgA | hgB
    · exact DA.admissible g hgA
    · exact DB.admissible g hgB
  isometry :=
    (DA.isometry.prod DB.isometry).trans
      (orthogonalSumNikulinGeneratorsAppendIsometry DA.generators DB.generators).symm

@[simp]
theorem generators_prod {A : FiniteQuadraticModule.{u}} {B : FiniteQuadraticModule.{v}}
    (DA : NikulinDecomposition A) (DB : NikulinDecomposition B) :
    (DA.prod DB).generators = DA.generators ++ DB.generators := (rfl)

/-- The canonical `NikulinDecomposition` of a `Fin n`-indexed orthogonal family of admissible
Nikulin generators. -/
noncomputable def piOfFn {n : ℕ} (f : Fin n → NikulinGenerator)
    (hf : ∀ i, (f i).IsAdmissible) :
    NikulinDecomposition (pi fun i ↦ (f i).toFiniteQuadraticModule) where
  generators := List.ofFn f
  admissible g hg := by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
    exact hf i
  isometry := piToOrthogonalSumNikulinGeneratorsIsometry f

@[simp]
theorem generators_piOfFn {n : ℕ} (f : Fin n → NikulinGenerator)
    (hf : ∀ i, (f i).IsAdmissible) :
    (piOfFn f hf).generators = List.ofFn f := (rfl)

/-- Any module admitting a `NikulinDecomposition` is nondegenerate. -/
theorem isNondegenerate {A : FiniteQuadraticModule.{u}} (D : NikulinDecomposition A) :
    A.IsNondegenerate :=
  D.isometry.isNondegenerate_iff.mpr (isNondegenerate_orthogonalSumNikulinGenerators D.admissible)

end NikulinDecomposition

/-! ## Existence for nondegenerate modules -/

private theorem exists_oddPrimePowGenerator (m : ℕ) (hm : Odd m) (θ : ℤ)
    (hm_pp : IsPrimePow m) (hθ : IsCoprime (m : ℤ) θ) :
    ∃ g : NikulinGenerator, g.IsAdmissible ∧
      Nonempty (Isometry (oddCyclic m hm θ) g.toFiniteQuadraticModule) := by
  obtain ⟨p, k, hp', hk, rfl⟩ := hm_pp
  have hp : p.Prime := Nat.prime_iff.mpr hp'
  have hodd : Odd p := by
    rcases hp.eq_two_or_odd' with rfl | hodd
    · exact absurd (even_two.pow_of_ne_zero hk.ne') (Nat.not_even_iff_odd.mpr hm)
    · exact hodd
  refine ⟨.oddCyclic p k hp hodd θ, ?_, ⟨QuadraticMap.IsometryEquiv.refl _⟩⟩
  exact (NikulinGenerator.isNondegenerate_toFiniteQuadraticModule_iff
    ((NikulinGenerator.exponent_oddCyclic p k hp hodd θ).symm ▸ hk)).mp
    ((isNondegenerate_oddCyclic_iff (p ^ k) hodd.pow θ).mpr hθ)

/-- Construct a `NikulinDecomposition` for any nondegenerate finite quadratic module via
`exists_isometry_prod_pi_generators`. -/
noncomputable def NikulinDecomposition.ofIsNondegenerate {A : FiniteQuadraticModule.{u}}
    (hA : A.IsNondegenerate) : NikulinDecomposition A :=
  Classical.choice <| by
    obtain ⟨a, m, hm, θ, b, k, η, c, ku, d, kv, hmθ, hη, ⟨f⟩⟩ :=
      exists_isometry_prod_pi_generators A hA
    have hOdd := fun i ↦ exists_oddPrimePowGenerator (m i) (hm i) (θ i) (hmθ i).1 (hmθ i).2
    let eOdd : Isometry (pi fun i ↦ oddCyclic (m i) (hm i) (θ i))
        (pi fun i ↦ ((hOdd i).choose).toFiniteQuadraticModule) :=
      QuadraticMap.IsometryEquiv.pi fun i ↦ (hOdd i).choose_spec.2.some
    let DOdd : NikulinDecomposition (pi fun i ↦ oddCyclic (m i) (hm i) (θ i)) :=
      (piOfFn (fun i ↦ (hOdd i).choose) fun i ↦ (hOdd i).choose_spec.1).ofIsometry eOdd
    let DDyadic : NikulinDecomposition (pi fun i ↦ dyadicCyclic (k i + 1) (η i)) :=
      piOfFn (fun i ↦ .dyadicCyclic (k i + 1) (Nat.succ_pos (k i)) (η i)) fun i ↦
        (NikulinGenerator.isAdmissible_dyadicCyclic _ _ _).mpr (hη i)
    let DU : NikulinDecomposition (pi fun i ↦ dyadicU (ku i + 1)) :=
      piOfFn (fun i ↦ .dyadicU (ku i + 1)) fun i ↦
        (NikulinGenerator.isAdmissible_dyadicU _).mpr (Nat.succ_pos (ku i))
    let DV : NikulinDecomposition (pi fun i ↦ dyadicV (kv i + 1)) :=
      piOfFn (fun i ↦ .dyadicV (kv i + 1)) fun i ↦
        (NikulinGenerator.isAdmissible_dyadicV _).mpr (Nat.succ_pos (kv i))
    exact ⟨(DOdd.prod (DDyadic.prod (DU.prod DV))).ofIsometry f.symm⟩

/-- A finite quadratic module admits a `NikulinDecomposition` if and only if it is
nondegenerate. -/
theorem nonempty_nikulinDecomposition_iff (A : FiniteQuadraticModule.{u}) :
    Nonempty (NikulinDecomposition A) ↔ A.IsNondegenerate :=
  ⟨fun ⟨D⟩ ↦ D.isNondegenerate, fun hA ↦ ⟨.ofIsNondegenerate hA⟩⟩

/-- A degenerate finite quadratic module admits no `NikulinDecomposition`. -/
theorem isEmpty_nikulinDecomposition_of_not_isNondegenerate {A : FiniteQuadraticModule.{u}}
    (hA : ¬ A.IsNondegenerate) : IsEmpty (NikulinDecomposition A) :=
  ⟨fun D ↦ hA D.isNondegenerate⟩

/-- Concrete degenerate check: `dyadicCyclic 1 2` (even parameter `θ = 2`) has no
`NikulinDecomposition`. -/
theorem isEmpty_nikulinDecomposition_dyadicCyclic_one_two :
    IsEmpty (NikulinDecomposition (dyadicCyclic 1 2)) :=
  isEmpty_nikulinDecomposition_of_not_isNondegenerate <| by
    rw [isNondegenerate_dyadicCyclic_iff]
    decide

/-! ## Primary filtering, generator ranks, and realization determinants -/

/-- Partitioning a list of Nikulin generators by a boolean predicate `P` splits its orthogonal sum
as an orthogonal product. -/
noncomputable def orthogonalSumNikulinGeneratorsPartitionIsometry (P : NikulinGenerator → Bool) :
    ∀ gs : List NikulinGenerator,
      Isometry (orthogonalSumNikulinGenerators gs)
        ((orthogonalSumNikulinGenerators (gs.filter P)).prod
          (orthogonalSumNikulinGenerators (gs.filter fun g ↦ !P g)))
  | [] => by
      simp only [List.filter_nil]
      letI : Subsingleton
          ((orthogonalSumNikulinGenerators []).prod (orthogonalSumNikulinGenerators [])).carrier :=
        inferInstanceAs (Subsingleton (PUnit.{1} × PUnit.{1}))
      exact Isometry.ofSubsingleton
  | g :: gs => by
      cases hP : P g
      · simp only [List.filter_cons, hP, Bool.not_false, orthogonalSumNikulinGenerators_cons]
        exact ((QuadraticMap.IsometryEquiv.refl _).prod
          (orthogonalSumNikulinGeneratorsPartitionIsometry P gs)).trans
          (QuadraticMap.IsometryEquiv.prodLeftComm _ _ _)
      · simp only [List.filter_cons, hP, Bool.not_true, orthogonalSumNikulinGenerators_cons]
        exact ((QuadraticMap.IsometryEquiv.refl _).prod
          (orthogonalSumNikulinGeneratorsPartitionIsometry P gs)).trans
          (QuadraticMap.IsometryEquiv.prodAssoc _ _ _).symm

/-- Taking the `p`-primary component of an orthogonal sum of Nikulin generators filters the list to
the generators with `g.prime = p`. -/
noncomputable def orthogonalSumPrimaryComponentIsometry {p : ℕ} (hp : p.Prime) :
    ∀ gs : List NikulinGenerator,
      Isometry ((orthogonalSumNikulinGenerators gs).primaryComponent p)
        (orthogonalSumNikulinGenerators (gs.filter fun g ↦ g.prime = p))
  | [] => by
      simp only [List.filter_nil]
      letI : Subsingleton ((orthogonalSumNikulinGenerators []).primaryComponent p).carrier :=
        inferInstanceAs (Subsingleton (_root_.AddCommGroup.primaryComponent PUnit.{1} p))
      exact Isometry.ofSubsingleton
  | g :: gs => by
      by_cases hgp : g.prime = p
      · have hdec : decide (g.prime = p) = true := decide_eq_true hgp
        simp only [List.filter_cons, hdec, orthogonalSumNikulinGenerators_cons]
        have hpow : ∃ m, Nat.card g.toFiniteQuadraticModule = p ^ m :=
          ⟨g.rank * g.exponent, by rw [g.natCard_toFiniteQuadraticModule, hgp]⟩
        exact (primaryComponentProdIsometry _ _ p).trans
          ((primaryComponentSelfIsometry _ hpow).prod
            (orthogonalSumPrimaryComponentIsometry hp gs))
      · have hdec : decide (g.prime = p) = false := decide_eq_false hgp
        simp only [List.filter_cons, hdec, orthogonalSumNikulinGenerators_cons]
        have hcop : (Nat.card g.toFiniteQuadraticModule).Coprime p := by
          rw [g.natCard_toFiniteQuadraticModule]
          exact ((Nat.coprime_primes g.prime_prime hp).mpr hgp).pow_left _
        have hsub : Subsingleton (g.toFiniteQuadraticModule.primaryComponent p) :=
          subsingleton_primaryComponent_of_coprime _ hcop
        letI : Unique (g.toFiniteQuadraticModule.primaryComponent p) :=
          ⟨⟨0⟩, fun x ↦ hsub.elim x 0⟩
        exact (primaryComponentProdIsometry _ _ p).trans
          ((QuadraticMap.IsometryEquiv.uniqueProd _ _).trans
            (orthogonalSumPrimaryComponentIsometry hp gs))

private theorem exists_natCard_orthogonalSum_eq_prime_pow {p : ℕ} :
    ∀ {gs : List NikulinGenerator}, (∀ g ∈ gs, g.prime = p) →
      ∃ e : ℕ, Nat.card (orthogonalSumNikulinGenerators gs) = p ^ e
  | [], _ => ⟨0, natCard_orthogonalSumNikulinGenerators []⟩
  | g :: gs, hgs => by
      obtain ⟨e, he⟩ := exists_natCard_orthogonalSum_eq_prime_pow
        (p := p) (fun g' hg' ↦ hgs g' (List.mem_cons_of_mem g hg'))
      refine ⟨g.rank * g.exponent + e, ?_⟩
      rw [orthogonalSumNikulinGenerators_cons, Nat.card_prod, g.natCard_toFiniteQuadraticModule,
        hgs g List.mem_cons_self, he, pow_add]

private theorem rank_orthogonalSumNikulinGenerators_of_prime {p : ℕ} (hp : p.Prime) :
    ∀ {gs : List NikulinGenerator},
      (∀ g ∈ gs, g.IsAdmissible) → (∀ g ∈ gs, g.prime = p) →
        AddGroup.rank (orthogonalSumNikulinGenerators gs) = (gs.map NikulinGenerator.rank).sum
  | [], _, _ => by
      rw [AddGroup.rank_eq_zero]
      rfl
  | g :: gs, hadm, hprime => by
      have hg_adm : g.IsAdmissible := hadm g List.mem_cons_self
      have hg_prime : g.prime = p := hprime g List.mem_cons_self
      have hadm' : ∀ g' ∈ gs, g'.IsAdmissible :=
        fun g' hg' ↦ hadm g' (List.mem_cons_of_mem g hg')
      have hprime' : ∀ g' ∈ gs, g'.prime = p :=
        fun g' hg' ↦ hprime g' (List.mem_cons_of_mem g hg')
      obtain ⟨e₂, he₂⟩ := exists_natCard_orthogonalSum_eq_prime_pow hprime'
      have he₁ : Nat.card g.toFiniteQuadraticModule = p ^ (g.rank * g.exponent) := by
        rw [g.natCard_toFiniteQuadraticModule, hg_prime]
      rw [orthogonalSumNikulinGenerators_cons]
      exact (TauCeti.AddCommGroup.rank_prod_of_prime_pow_card hp he₁ he₂).trans <| by
        rw [NikulinGenerator.rank_toFiniteQuadraticModule hg_adm,
          rank_orthogonalSumNikulinGenerators_of_prime hp hadm' hprime',
          List.map_cons, List.sum_cons]

private theorem ordProj_natAbs_prod_realizationDet {p : ℕ} (hp : p.Prime) :
    ∀ {gs : List NikulinGenerator},
      (∀ g ∈ gs, g.IsAdmissible) → (∀ g ∈ gs, g.prime = p) →
        ordProj[p] ((gs.map NikulinGenerator.realizationDet).prod).natAbs =
          Nat.card (orthogonalSumNikulinGenerators gs)
  | [], _, _ => by
      rw [natCard_orthogonalSumNikulinGenerators []]
      simp
  | g :: gs, hadm, hprime => by
      have hg_adm : g.IsAdmissible := hadm g List.mem_cons_self
      have hg_prime : g.prime = p := hprime g List.mem_cons_self
      have hadm' : ∀ g' ∈ gs, g'.IsAdmissible :=
        fun g' hg' ↦ hadm g' (List.mem_cons_of_mem g hg')
      have hprime' : ∀ g' ∈ gs, g'.prime = p :=
        fun g' hg' ↦ hprime g' (List.mem_cons_of_mem g hg')
      have hne₁ : g.realizationDet.natAbs ≠ 0 :=
        Int.natAbs_ne_zero.mpr (NikulinGenerator.realizationDet_ne_zero hg_adm)
      have hne₂ : ((gs.map NikulinGenerator.realizationDet).prod).natAbs ≠ 0 := by
        rw [Int.natAbs_ne_zero]
        refine List.prod_ne_zero fun h0 ↦ ?_
        obtain ⟨g', hg', hdet⟩ := List.mem_map.mp h0
        exact NikulinGenerator.realizationDet_ne_zero (hadm' g' hg') hdet
      rw [List.map_cons, List.prod_cons, Int.natAbs_mul, Nat.ordProj_mul p hne₁ hne₂,
        ← hg_prime, NikulinGenerator.ordProj_natAbs_realizationDet hg_adm, hg_prime,
        ordProj_natAbs_prod_realizationDet hp hadm' hprime',
        orthogonalSumNikulinGenerators_cons, Nat.card_prod]

namespace NikulinDecomposition

variable {A : FiniteQuadraticModule.{u}} (D : NikulinDecomposition A)

/-- The cardinality of `A` equals the product of the generator cardinalities in `D`. -/
theorem natCard_eq :
    Nat.card A = (D.generators.map fun g ↦ g.prime ^ (g.rank * g.exponent)).prod := by
  rw [Nat.card_congr D.isometry.toLinearEquiv.toEquiv, natCard_orthogonalSumNikulinGenerators]
  congr 1
  exact List.map_congr_left fun g _ ↦ g.natCard_toFiniteQuadraticModule

/-- The Gauss-sum invariant of `A` equals the sum of the Gauss-sum invariants of the generators in
`D`. -/
theorem gaussSign_eq :
    A.gaussSign = (D.generators.map fun g ↦ g.toFiniteQuadraticModule.gaussSign).sum :=
  D.isometry.gaussSign_eq.trans (gaussSign_orthogonalSumNikulinGenerators D.admissible)

/-- Filtering a `NikulinDecomposition` of `A` to a prime `p` produces a `NikulinDecomposition` of
the `p`-primary component `A.primaryComponent p`. -/
noncomputable def primaryComponent {p : ℕ} (hp : p.Prime) :
    NikulinDecomposition (A.primaryComponent p) where
  generators := D.generators.filter fun g ↦ g.prime = p
  admissible g hg := D.admissible g (List.mem_of_mem_filter hg)
  isometry :=
    (D.isometry.primaryComponent p).trans (orthogonalSumPrimaryComponentIsometry hp D.generators)

@[simp]
theorem generators_primaryComponent {p : ℕ} (hp : p.Prime) :
    (D.primaryComponent hp).generators = D.generators.filter fun g ↦ g.prime = p := (rfl)

/-- **Primary generator rank from a Nikulin decomposition.** For any prime `p`, the additive
generator rank `AddGroup.rank (A.primaryComponent p)` (`l(A_{q_p})` in Nikulin's notation) is the
sum of `NikulinGenerator.rank` (`1` on cyclic summands, `2` on `u` and `v`) over the `p`-primary
generators in `D`. -/
theorem rank_primaryComponent_eq {p : ℕ} (hp : p.Prime) :
    AddGroup.rank (A.primaryComponent p) =
      ((D.generators.filter fun g ↦ g.prime = p).map NikulinGenerator.rank).sum := by
  have hcongr := AddGroup.rank_congr (D.primaryComponent hp).isometry.toAddEquiv
  have hadm : ∀ g ∈ D.generators.filter (fun g ↦ g.prime = p), g.IsAdmissible :=
    fun g hg ↦ D.admissible g (List.mem_of_mem_filter hg)
  have hprime : ∀ g ∈ D.generators.filter (fun g ↦ g.prime = p), g.prime = p :=
    fun g hg ↦ of_decide_eq_true (List.mem_filter.mp hg).2
  rw [hcongr, generators_primaryComponent]
  exact rank_orthogonalSumNikulinGenerators_of_prime hp hadm hprime

/-- **Global generator rank (`l(A_q)`) from a Nikulin decomposition.** The minimal number of
additive generators of `A` is the supremum over its prime factors of the summed formal ranks of the
corresponding primary generators in `D`. -/
theorem rank_eq :
    AddGroup.rank A =
      Finset.univ.sup fun p : (Nat.card A).primeFactors ↦
        ((D.generators.filter fun g ↦ g.prime = p.1).map NikulinGenerator.rank).sum := by
  rw [A.rank_eq_sup_primaryComponent]
  exact Finset.sup_congr rfl fun p _ ↦
    D.rank_primaryComponent_eq (Nat.prime_of_mem_primeFactors p.2)

/-- The product of the minimal `p`-adic realization Gram determinants of the generators in `D`
having prime `p` (the integer representative of Nikulin's `discr K(q_p)` in Theorem 1.9.1). -/
def realizationDetProd (p : ℕ) : ℤ :=
  ((D.generators.filter fun g ↦ g.prime = p).map NikulinGenerator.realizationDet).prod

@[simp]
theorem realizationDetProd_def (p : ℕ) :
    D.realizationDetProd p =
      ((D.generators.filter fun g ↦ g.prime = p).map NikulinGenerator.realizationDet).prod := (rfl)

/-- The `p`-primary realization determinant product of a `NikulinDecomposition` is nonzero. -/
theorem realizationDetProd_ne_zero (p : ℕ) : D.realizationDetProd p ≠ 0 := by
  rw [realizationDetProd_def]
  refine List.prod_ne_zero fun h0 ↦ ?_
  obtain ⟨g, hg, hdet⟩ := List.mem_map.mp h0
  exact NikulinGenerator.realizationDet_ne_zero (D.admissible g (List.mem_of_mem_filter hg)) hdet

/-- For every prime `p`, the `p`-primary part of `|D.realizationDetProd p|` equals the cardinality
of `A.primaryComponent p`. -/
theorem ordProj_natAbs_realizationDetProd {p : ℕ} (hp : p.Prime) :
    ordProj[p] (D.realizationDetProd p).natAbs = Nat.card (A.primaryComponent p) := by
  have hadm : ∀ g ∈ D.generators.filter (fun g ↦ g.prime = p), g.IsAdmissible :=
    fun g hg ↦ D.admissible g (List.mem_of_mem_filter hg)
  have hprime : ∀ g ∈ D.generators.filter (fun g ↦ g.prime = p), g.prime = p :=
    fun g hg ↦ of_decide_eq_true (List.mem_filter.mp hg).2
  rw [realizationDetProd_def, ordProj_natAbs_prod_realizationDet hp hadm hprime,
    Nat.card_congr (D.primaryComponent hp).isometry.toLinearEquiv.toEquiv,
    generators_primaryComponent]

end NikulinDecomposition

/-! ## Dyadic cyclic summands of order two and non-uniqueness -/

/-- **The dyadic boundary predicate of Nikulin's Theorem 1.10.1(4)**: `A` splits off a cyclic
summand `q_θ^{(2)}(2)` of order two with `θ` odd. -/
def HasCyclicTwoSummand (A : FiniteQuadraticModule.{u}) : Prop :=
  ∃ (θ : ℤ) (A' : FiniteQuadraticModule.{0}),
    Odd θ ∧ Nonempty (A.Isometry ((dyadicCyclic 1 θ).prod A'))

/-- `HasCyclicTwoSummand` is invariant under quadratic isometry. -/
theorem Isometry.hasCyclicTwoSummand_iff {A : FiniteQuadraticModule.{u}}
    {B : FiniteQuadraticModule.{v}} (f : A.Isometry B) :
    HasCyclicTwoSummand A ↔ HasCyclicTwoSummand B := by
  refine ⟨?_, ?_⟩
  · rintro ⟨θ, A', hθ, ⟨e⟩⟩
    exact ⟨θ, A', hθ, ⟨f.symm.trans e⟩⟩
  · rintro ⟨θ, B', hθ, ⟨e⟩⟩
    exact ⟨θ, B', hθ, ⟨f.trans e⟩⟩

/-- Splitting off `dyadicCyclic 1 θ` (`θ` odd) with a nondegenerate complement `B` in any universe
implies `HasCyclicTwoSummand A`. -/
theorem hasCyclicTwoSummand_of_isometry_prod {A : FiniteQuadraticModule.{u}}
    {B : FiniteQuadraticModule.{v}} (hB : B.IsNondegenerate) {θ : ℤ} (hθ : Odd θ)
    (f : A.Isometry ((dyadicCyclic 1 θ).prod B)) :
    HasCyclicTwoSummand A :=
  ⟨θ, orthogonalSumNikulinGenerators (NikulinDecomposition.ofIsNondegenerate hB).generators, hθ,
    ⟨f.trans ((QuadraticMap.IsometryEquiv.refl _).prod
      (NikulinDecomposition.ofIsNondegenerate hB).isometry)⟩⟩

/-- If a `NikulinDecomposition` of `A` contains a label `.dyadicCyclic 1 hk θ`, then
`HasCyclicTwoSummand A` holds. -/
theorem NikulinDecomposition.hasCyclicTwoSummand_of_mem {A : FiniteQuadraticModule.{u}}
    (D : NikulinDecomposition A) {hk : 0 < 1} {θ : ℤ}
    (hmem : .dyadicCyclic 1 hk θ ∈ D.generators) :
    HasCyclicTwoSummand A := by
  have hθ : Odd θ := (NikulinGenerator.isAdmissible_dyadicCyclic 1 hk θ).mp (D.admissible _ hmem)
  exact ⟨θ, orthogonalSumNikulinGenerators (D.generators.erase (.dyadicCyclic 1 hk θ)), hθ,
    ⟨D.isometry.trans (orthogonalSumNikulinGeneratorsEraseIsometry _ hmem)⟩⟩

/-- If `A` splits off a cyclic summand `q_θ^{(2)}(2)` (`θ` odd), then `A` contains a `2`-torsion
element `x` with `q(x) + q(x) ≠ 0`. -/
theorem HasCyclicTwoSummand.exists_two_nsmul_eq_zero_and_quadratic_add_self_ne_zero
    {A : FiniteQuadraticModule.{u}} (h : HasCyclicTwoSummand A) :
    ∃ x : A, 2 • x = 0 ∧ A.quadratic x + A.quadratic x ≠ 0 := by
  obtain ⟨θ, A', hθ, ⟨f⟩⟩ := h
  have hx₀' : (2 : ℕ) • (1 : ZMod (2 ^ 1)) = 0 := by decide
  let x₀ : dyadicCyclic 1 θ := (1 : ZMod (2 ^ 1))
  have hx₀ : 2 • x₀ = 0 := hx₀'
  refine ⟨f.symm (x₀, 0), ?_, ?_⟩
  · rw [← map_nsmul, Prod.smul_mk, hx₀, smul_zero]
    exact map_zero f.symm
  · have hq : A.quadratic (f.symm (x₀, 0)) = (dyadicCyclic 1 θ).quadratic x₀ := by
      rw [f.symm.map_app, prod_quadratic, QuadraticMap.map_zero, add_zero]
    rw [hq]
    exact dyadicCyclic_one_quadratic_add_self_ne_zero hθ

/-- For a nondegenerate finite quadratic module `A`, the `2`-primary component
`A.primaryComponent 2` splits off a cyclic summand `q_θ^{(2)}(2)` if and only if `A` itself
does. -/
theorem hasCyclicTwoSummand_primaryComponent_two_iff {A : FiniteQuadraticModule.{u}}
    (hA : A.IsNondegenerate) :
    HasCyclicTwoSummand (A.primaryComponent 2) ↔ HasCyclicTwoSummand A := by
  refine ⟨?_, ?_⟩
  · rintro ⟨θ, B₂, hθ, ⟨f₂⟩⟩
    let D := NikulinDecomposition.ofIsNondegenerate hA
    let B_odd := orthogonalSumNikulinGenerators (D.generators.filter fun g ↦ !(g.prime = 2))
    have eSplit : A.Isometry ((A.primaryComponent 2).prod B_odd) :=
      (D.isometry.trans
        (orthogonalSumNikulinGeneratorsPartitionIsometry (fun g ↦ g.prime = 2) D.generators)).trans
        ((D.primaryComponent Nat.prime_two).isometry.symm.prod
          (QuadraticMap.IsometryEquiv.refl B_odd.quadratic))
    exact ⟨θ, B₂.prod B_odd, hθ,
      ⟨(eSplit.trans (f₂.prod (QuadraticMap.IsometryEquiv.refl B_odd.quadratic))).trans
        (QuadraticMap.IsometryEquiv.prodAssoc _ _ _)⟩⟩
  · rintro ⟨θ, A', hθ, ⟨f⟩⟩
    have hpow : ∃ m, Nat.card (dyadicCyclic 1 θ) = 2 ^ m := ⟨1, natCard_dyadicCyclic 1 θ⟩
    exact ⟨θ, A'.primaryComponent 2, hθ,
      ⟨(f.primaryComponent 2).trans
        ((primaryComponentProdIsometry _ _ 2).trans
          ((primaryComponentSelfIsometry _ hpow).prod (QuadraticMap.IsometryEquiv.refl _)))⟩⟩

/-- On a nondegenerate `2`-elementary finite quadratic module (`∀ x, 2 • x = 0`),
`HasCyclicTwoSummand A` holds if and only if the quadratic form does not take all its values in
`½ℤ/ℤ`. -/
theorem hasCyclicTwoSummand_iff_of_two_nsmul_eq_zero {A : FiniteQuadraticModule.{u}}
    (hA : A.IsNondegenerate) (h2 : ∀ x : A, 2 • x = 0) :
    HasCyclicTwoSummand A ↔ ¬ ∀ x : A, A.quadratic x + A.quadratic x = 0 := by
  refine ⟨fun h hall ↦ ?_, fun hnot ↦ ?_⟩
  · obtain ⟨x, -, hne⟩ := h.exists_two_nsmul_eq_zero_and_quadratic_add_self_ne_zero
    exact hne (hall x)
  · obtain ⟨b, η, c, d, hη, ⟨f⟩⟩ := exists_isometry_prod_pi_of_two_nsmul_eq_zero A hA h2
    cases b with
    | zero =>
        exfalso
        apply hnot
        rw [← f.forall_quadratic_add_self_eq_zero_iff, forall_quadratic_add_self_eq_zero_prod_iff,
          forall_quadratic_add_self_eq_zero_prod_iff, forall_quadratic_add_self_eq_zero_pi_iff,
          forall_quadratic_add_self_eq_zero_pi_iff, forall_quadratic_add_self_eq_zero_pi_iff]
        exact ⟨fun i ↦ i.elim0, fun _ ↦ dyadicU_one_quadratic_add_self_eq_zero,
          fun _ ↦ dyadicV_one_quadratic_add_self_eq_zero⟩
    | succ b =>
        let R := (pi fun i : Fin b ↦ dyadicCyclic 1 (η i.succ)).prod
          ((pi fun _ : Fin c ↦ dyadicU 1).prod (pi fun _ : Fin d ↦ dyadicV 1))
        let split : Isometry ((dyadicCyclic 1 (η 0)).prod R) A :=
          (QuadraticMap.IsometryEquiv.prodAssoc _ _ _).symm.trans
            (((QuadraticMap.IsometryEquiv.consPi _).prod
              (QuadraticMap.IsometryEquiv.refl _)).trans f)
        exact ⟨η 0, R, hη 0, ⟨split.symm⟩⟩

/-- **Non-uniqueness of `NikulinDecomposition` labels** (Nikulin, Proposition 1.8.2(b)):
`(dyadicU 1).prod (dyadicU 1)` admits decompositions with distinct generator lists
`[.dyadicU 1, .dyadicU 1]` and `[.dyadicV 1, .dyadicV 1]`. -/
theorem exists_ne_generators_nikulinDecomposition :
    ∃ D₁ D₂ : NikulinDecomposition ((dyadicU 1).prod (dyadicU 1)),
      D₁.generators ≠ D₂.generators := by
  let D₁ : NikulinDecomposition ((dyadicU 1).prod (dyadicU 1)) :=
    { generators := [.dyadicU 1, .dyadicU 1]
      admissible := by
        intro g hg
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl <;> exact (NikulinGenerator.isAdmissible_dyadicU 1).mpr Nat.one_pos
      isometry := (orthogonalSumNikulinGeneratorsPairIsometry (.dyadicU 1) (.dyadicU 1)).symm }
  let D₂ : NikulinDecomposition ((dyadicU 1).prod (dyadicU 1)) :=
    { generators := [.dyadicV 1, .dyadicV 1]
      admissible := by
        intro g hg
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl <;> exact (NikulinGenerator.isAdmissible_dyadicV 1).mpr Nat.one_pos
      isometry := (dyadicUProdSelfIsometryDyadicVProdSelf 1).trans
        (orthogonalSumNikulinGeneratorsPairIsometry (.dyadicV 1) (.dyadicV 1)).symm }
  refine ⟨D₁, D₂, fun h ↦ ?_⟩
  nomatch h

end TauCeti.FiniteQuadraticModule
