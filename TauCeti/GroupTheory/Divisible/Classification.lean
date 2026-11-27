/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AddCircle
public import TauCeti.GroupTheory.Divisible.MaxDivisible
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.Field.ZMod

import TauCeti.Algebra.Module.Torsion.Essential
import TauCeti.Algebra.Module.LocalizedModule.Basic
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import TauCeti.GroupTheory.Torsion
import Mathlib.Algebra.Category.Grp.Injective

/-!
# Classification of divisible abelian groups

We realize the Prüfer group at a prime `p` as the `p`-primary component of the rational
circle `ℚ/ℤ`. A basis of the `p`-torsion of a divisible `p`-primary group extends to a direct
sum decomposition into copies of this group. Combining these primary decompositions with a
splitting of the torsion subgroup gives `nonempty_addEquiv_rat_pruferSum`: every divisible
abelian group is a direct sum of rational copies and prime-indexed Prüfer copies. The copies
are indexed by bases of the torsion-free quotient and the `p`-torsion of the original group,
respectively, so their cardinalities are intrinsic.

`nonempty_ratModule` supplies the unique rational structure on a divisible torsion-free
group. All classification results accept caller-chosen bases and scalar structures.

## References

* L. Fuchs, *Abelian Groups* (2015), Chapter 4, Theorem 3.1, pp. 140–141.
* C. Weibel, *The K-book*, proof of Lemma VI.1.6 and Proposition VI.7.3.
-/

public section

namespace TauCeti

open AddSubgroup

/-- For prime `p`, the Prüfer `p`-group, realized inside the rational circle `ℚ/ℤ`. -/
abbrev prufer (p : ℕ) := AddCommGroup.primaryComponent (AddCircle (1 : ℚ)) p

private theorem isDivisible_primaryComponent {A : Type*} [AddCommGroup A] [DivisibleBy A ℕ]
    (p : ℕ) (hp : p.Prime) : (AddCommGroup.primaryComponent A p).IsDivisible := by
  rw [AddSubgroup.isDivisible_def]
  intro n hn x hx
  obtain ⟨y, hy⟩ : ∃ y : A, n • y = x := DivisibleBy.surjective_smul A ℕ hn x
  obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp hx
  have hyfin : IsOfFinAddOrder y := isOfFinAddOrder_iff_nsmul_eq_zero.mpr
    ⟨p ^ k * n, Nat.mul_pos (pow_pos hp.pos _) (Nat.pos_of_ne_zero hn), by
      rw [← smul_smul, hy, hk]⟩
  obtain ⟨y', hy', heq⟩ := exists_mem_primaryComponent_apply_eq
    (nsmulAddMonoidHom (α := A) n) hp hyfin (AddCommMonoid.mem_primaryComponent.mpr ⟨k, by
      simpa only [nsmulAddMonoidHom_apply, hy] using hk⟩)
  exact ⟨y', hy', heq.trans hy⟩

/-- For prime `p`, the Prüfer subgroup of the rational circle is divisible. -/
theorem isDivisible_prufer (p : ℕ) [Fact p.Prime] : (prufer p).IsDivisible := by
  let : DivisibleBy (AddCircle (1 : ℚ)) ℕ :=
    AddGroup.divisibleByNatOfDivisibleByInt _
  exact isDivisible_primaryComponent p (Fact.out : p.Prime)

/-- The canonical embedding of the order-`p` cyclic group in the Prüfer group. -/
def pruferTorsion (p : ℕ) : ZMod p →+ prufer p where
  toFun x := ⟨ZMod.toRatAddCircle p x, 1, by
    have hx : p • ZMod.toRatAddCircle p x = 0 := by rw [← map_nsmul]; simp
    simpa using hx⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x y)

/-- The cyclic embedding agrees with the rational-circle character. -/
@[simp]
theorem pruferTorsion_coe (p : ℕ) (a : ZMod p) :
    (pruferTorsion p a : AddCircle (1 : ℚ)) = ZMod.toRatAddCircle p a := by
  simp only [pruferTorsion, AddMonoidHom.coe_mk, ZeroHom.coe_mk]

/-- The canonical cyclic embedding in a Prüfer group is injective. -/
theorem pruferTorsion_injective (p : ℕ) [NeZero p] : Function.Injective (pruferTorsion p) :=
  fun _ _ h ↦ ZMod.toRatAddCircle_injective p (congrArg Subtype.val h)

/-- The image of the canonical cyclic embedding is exactly the `p`-torsion. -/
theorem pruferTorsion_range (p : ℕ) [NeZero p] :
    (pruferTorsion p).range = (prufer p)[p] := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    rw [AddSubgroup.torsionBy.nsmul_iff, ← map_nsmul]
    simp
  · intro hx
    obtain ⟨a, ha⟩ := ZMod.exists_toRatAddCircle_eq_of_nsmul_eq_zero p
      (congrArg Subtype.val (AddSubgroup.torsionBy.nsmul_iff.mp hx))
    exact ⟨a, Subtype.ext ha⟩

private theorem finsupp_isAddPGroup {ι M : Type*} [AddCommGroup M] {p : ℕ}
    (hM : IsAddPGroup p M) : IsAddPGroup p (ι →₀ M) := by
  classical
  intro x
  induction x using Finsupp.induction with
  | zero => exact ⟨0, by simp⟩
  | single_add i a x _ _ ih =>
    obtain ⟨m, hm⟩ := hM a
    obtain ⟨n, hn⟩ := ih
    refine ⟨m + n, ?_⟩
    rw [smul_add, Finsupp.smul_single, pow_add]
    rw [mul_comm (p ^ m) (p ^ n), ← smul_smul, hm, smul_zero, Finsupp.single_zero,
      zero_add]
    rw [mul_comm, ← smul_smul, hn, smul_zero]

private theorem injective_of_isAddPGroup {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    {p : ℕ} (hM : IsAddPGroup p M) (f : M →+ N)
    (hf : ∀ x : M, p • x = 0 → f x = 0 → x = 0) : Function.Injective f := by
  have htop : (Ideal.span {(p : ℤ)}).primaryComponent M = ⊤ := by
    ext x
    simp only [Ideal.mem_primaryComponent_span_singleton_iff, Submodule.mem_top, iff_true,
      ← Int.natCast_pow, natCast_zsmul]
    exact hM x
  apply (injective_iff_disjoint_torsionBySet_ker (g := f.toIntLinearMap) htop).mpr
  rw [Submodule.disjoint_def]
  intro x hx hfx
  apply hf x
  · rw [Submodule.torsionBySet_ideal_span_singleton_eq, Submodule.mem_torsionBy_iff] at hx
    simpa only [natCast_zsmul] using hx
  · exact hfx

private theorem finsupp_isDivisible {ι M : Type*} [AddCommGroup M] [DivisibleBy M ℕ] :
    (⊤ : AddSubgroup (ι →₀ M)).IsDivisible := by
  rw [AddSubgroup.isDivisible_top_iff]
  intro n hn x
  obtain ⟨y, hy⟩ := Finsupp.mapRange_surjective (fun a : M ↦ n • a) (smul_zero n)
    (DivisibleBy.surjective_smul M ℕ hn) x
  exact ⟨y, by ext i; exact congrArg (fun f : ι →₀ M ↦ f i) hy⟩

section Primary

variable {A ι : Type*} [AddCommGroup A] {p : ℕ}

attribute [local instance] AddSubgroup.torsionBy.zmodModule

variable [Module (ZMod p) A[p]]

private theorem exists_prufer_hom [NeZero p] [DivisibleBy A ℕ] (v : A[p]) :
    ∃ f : prufer p →+ A, ∀ a : ZMod p, f (pruferTorsion p a) = ((a • v : A[p]) : A) := by
  let : DivisibleBy A ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  let g : ZMod p →+ A := (A[p]).subtype.comp
    (LinearMap.toSpanSingleton (ZMod p) A[p] v).toAddMonoidHom
  obtain ⟨f, hf⟩ := (Module.Baer.of_divisible A).extension_property_addMonoidHom
    (pruferTorsion p) (pruferTorsion_injective p) g
  exact ⟨f, fun a ↦ DFunLike.congr_fun hf a⟩

/-- A basis of the `p`-torsion of a divisible group extends to an injective map from a direct
sum of Prüfer groups, taking each canonical cyclic subgroup to its prescribed basis line. -/
theorem exists_injective_pruferSum [NeZero p] [DivisibleBy A ℕ]
    (b : Module.Basis ι (ZMod p) A[p]) :
    ∃ f : (ι →₀ prufer p) →+ A, Function.Injective f ∧
      f.comp (Finsupp.mapRange.addMonoidHom (pruferTorsion p)) =
        (A[p]).subtype.comp b.repr.symm.toAddMonoidHom := by
  classical
  choose g hg using fun i ↦ exists_prufer_hom (b i)
  let f := Finsupp.liftAddHom g
  have hcomp : f.comp (Finsupp.mapRange.addMonoidHom (pruferTorsion p)) =
      (A[p]).subtype.comp b.repr.symm.toAddMonoidHom := by
    ext i a
    simp [f, hg]
  refine ⟨f, injective_of_isAddPGroup
    (finsupp_isAddPGroup (fun x : prufer p ↦
      x.property.imp fun _ hk ↦ Subtype.ext hk)) f ?_, hcomp⟩
  · intro x hx hfx
    have hmem : x ∈ Set.range (Finsupp.mapRange (pruferTorsion p) (map_zero _)) := by
      rw [Finsupp.range_mapRange]
      intro i
      rw [← AddMonoidHom.coe_range, SetLike.mem_coe, pruferTorsion_range,
        AddSubgroup.torsionBy.nsmul_iff]
      exact congrArg (fun y : ι →₀ prufer p ↦ y i) hx
    obtain ⟨a, rfl⟩ := hmem
    have ha : b.repr.symm a = 0 := Subtype.ext <|
      (DFunLike.congr_fun hcomp a).symm.trans hfx
    have ha0 : a = 0 := b.repr.symm.injective (ha.trans b.repr.symm.map_zero.symm)
    simp [ha0]

/-- A divisible `p`-primary abelian group is a direct sum of Prüfer `p`-groups, with copies
indexed by any chosen basis of its intrinsic `p`-torsion vector space. -/
theorem nonempty_addEquiv_pruferSum [Fact p.Prime] [DivisibleBy A ℕ] (hA : IsAddPGroup p A)
    (b : Module.Basis ι (ZMod p) A[p]) : Nonempty (A ≃+ (ι →₀ prufer p)) := by
  classical
  obtain ⟨f, hf, hcomp⟩ := exists_injective_pruferSum b
  have hdiv : f.range.IsDivisible := by
    obtain ⟨_⟩ := isDivisible_iff_nonempty_divisibleBy.mp (isDivisible_prufer p)
    have h := (finsupp_isDivisible (ι := ι) (M := prufer p)).map f
    rwa [AddSubgroup.map_top] at h
  obtain ⟨r, hr⟩ := hdiv.exists_retraction
  have hpker : ∀ x : A, p • x = 0 → r x = 0 → x = 0 := by
    intro x hx hrx
    let v : A[p] := ⟨x, AddSubgroup.torsionBy.nsmul_iff.mpr hx⟩
    have hv : (v : A) ∈ f.range := by
      let a := b.repr v
      refine ⟨Finsupp.mapRange (pruferTorsion p) (map_zero _) a, ?_⟩
      exact (DFunLike.congr_fun hcomp a).trans
        (congrArg Subtype.val (b.repr.symm_apply_apply v))
    have heq := hr ⟨x, hv⟩
    rw [hrx] at heq
    exact (congrArg Subtype.val heq).symm
  have hinj := injective_of_isAddPGroup hA r hpker
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨y, hy⟩ := (r x).property
    refine ⟨y, hinj ?_⟩
    have hy' : f y = (r x : A) := hy
    rw [hy', hr]
  exact ⟨(AddEquiv.ofBijective f ⟨hf, hsurj⟩).symm⟩

end Primary

section Torsion

open IsDedekindDomain
open scoped DirectSum

private theorem primaryComponent_eq_ideal (A : Type*) [AddCommGroup A] (p : Nat.Primes) :
    (AddCommGroup.primaryComponent A p).toIntSubmodule =
      ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm p).asIdeal.primaryComponent A := by
  have he : Rat.IsIntegralClosure.intEquiv ℤ = RingEquiv.refl ℤ := by
    ext n
    simp
  have hgen := Rat.HeightOneSpectrum.span_natGenerator
    ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm p)
  have hpr := congrArg Subtype.val
    ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).apply_symm_apply p)
  -- The value of the prime subtype is the natural generator by definition of primesEquiv.
  change Rat.HeightOneSpectrum.natGenerator _ = (p : ℕ) at hpr
  rw [hpr, he] at hgen
  -- Ideal.map_id rewrites the ring homomorphism underlying the identity ring equivalence.
  change Ideal.span {(p : ℤ)} = Ideal.map (RingHom.id ℤ) _ at hgen
  rw [Ideal.map_id] at hgen
  rw [← hgen]
  ext x
  -- Passing from an additive subgroup to an integer submodule preserves its carrier.
  change x ∈ AddCommGroup.primaryComponent A p ↔ _
  simp only [AddCommGroup.mem_primaryComponent,
    Ideal.mem_primaryComponent_span_singleton_iff, ← Int.natCast_pow, natCast_zsmul]

private theorem nonempty_addEquiv_primarySum {A : Type*} [AddCommGroup A]
    (hA : IsAddTorsion A) :
    Nonempty (A ≃+ ⨁ p : Nat.Primes, AddCommGroup.primaryComponent A p) := by
  classical
  let C := fun p : Nat.Primes ↦ (AddCommGroup.primaryComponent A p).toIntSubmodule
  have hi : iSupIndep C := by
    simp only [C, primaryComponent_eq_ideal]
    exact (Ideal.iSupIndep_primaryComponent ℤ A).comp
      (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm.injective
  have hs : iSup C = ⊤ := by
    simp only [C, primaryComponent_eq_ideal]
    -- Display the composed family so iSup_comp can reindex it along the prime equivalence.
    change (⨆ p, (fun P : HeightOneSpectrum ℤ ↦ P.asIdeal.primaryComponent A)
      ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm p)) = ⊤
    exact ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm.surjective.iSup_comp
      (fun P : HeightOneSpectrum ℤ ↦ P.asIdeal.primaryComponent A)).trans
      (Ideal.iSup_primaryComponent_eq_top (isAddTorsion_iff_isTorsion_int.mp hA))
  have h := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hi hs
  exact ⟨(AddEquiv.ofBijective (DirectSum.coeAddMonoidHom C) h).symm⟩

attribute [local instance] AddSubgroup.torsionBy.zmodModule

private noncomputable def torsionBySubgroupEquiv (A : Type*) [AddCommGroup A]
    (D : AddSubgroup A) (n : ℕ) [Module (ZMod n) A[n]] [Module (ZMod n) D[n]]
    (hD : A[n] ≤ D) : A[n] ≃ₗ[ZMod n] D[n] := by
  let f : A[n] →+ D[n] :=
    { toFun := fun x ↦ ⟨⟨x, hD x.property⟩, Subtype.ext x.property⟩
      map_zero' := Subtype.ext (Subtype.ext rfl)
      map_add' := fun _ _ ↦ Subtype.ext (Subtype.ext rfl) }
  exact LinearEquiv.ofBijective (f.toZModLinearMap n)
    ⟨fun _ _ h ↦ Subtype.ext (congrArg (fun x ↦ x.val.val) h),
      fun y ↦ ⟨⟨y.val.val, congrArg Subtype.val y.property⟩, rfl⟩⟩

/-- A divisible torsion abelian group is a direct sum, over the primes, of Prüfer groups.
For each prime the copies are indexed by a basis of the group's own `p`-torsion. -/
theorem nonempty_addEquiv_torsion_pruferSum {A : Type*} [AddCommGroup A] [DivisibleBy A ℕ]
    (hA : IsAddTorsion A) {ι : Nat.Primes → Type*}
    [∀ p : Nat.Primes, Module (ZMod p) A[(p : ℤ)]]
    (b : ∀ p : Nat.Primes, Module.Basis (ι p) (ZMod p) A[(p : ℤ)]) :
    Nonempty (A ≃+ ⨁ p : Nat.Primes, (ι p →₀ prufer p)) := by
  classical
  have hex (p : Nat.Primes) :
      Nonempty (AddCommGroup.primaryComponent A p ≃+ (ι p →₀ prufer p)) := by
    let : Fact (p : ℕ).Prime := ⟨p.property⟩
    obtain ⟨_⟩ := isDivisible_iff_nonempty_divisibleBy.mp
      (isDivisible_primaryComponent (A := A) p p.property)
    exact nonempty_addEquiv_pruferSum
      (fun x ↦ x.property.imp fun _ hx ↦ Subtype.ext hx)
      ((b p).map (torsionBySubgroupEquiv A _ p fun x hx ↦
        ⟨1, by simpa only [pow_one] using torsionBy.nsmul_iff.mp hx⟩))
  let e := fun p ↦ Classical.choice (hex p)
  obtain ⟨eA⟩ := nonempty_addEquiv_primarySum hA
  exact ⟨eA.trans (DFinsupp.mapRange.addEquiv e)⟩

end Torsion

section Rational

open scoped nonZeroDivisors DirectSum

/-- A divisible abelian group with injective multiplication by positive integers has a
rational vector-space structure. It is unique by `subsingleton_rat_module`. -/
theorem nonempty_ratModule (A : Type*) [AddCommGroup A] [DivisibleBy A ℕ] [HasUniqueDiv A] :
    Nonempty (Module ℚ A) := by
  let : DivisibleBy A ℤ := AddGroup.divisibleByIntOfDivisibleByNat A
  let : IsLocalizedModule ℤ⁰ (LinearMap.id : A →ₗ[ℤ] A) :=
    isLocalizedModule_id_of_bijective_smul fun n hn ↦
      ⟨zsmul_right_injective (nonZeroDivisors.ne_zero hn),
        DivisibleBy.surjective_smul A ℤ (nonZeroDivisors.ne_zero hn)⟩
  exact ⟨IsLocalizedModule.module (A := ℚ) ℤ⁰ (LinearMap.id : A →ₗ[ℤ] A)⟩

attribute [local instance] AddSubgroup.torsionBy.zmodModule

private theorem isDivisible_torsion {A : Type*} [AddCommGroup A] [DivisibleBy A ℕ] :
    (AddCommGroup.torsion A).IsDivisible := by
  rw [isDivisible_def]
  intro n hn x hx
  obtain ⟨y, hy⟩ : ∃ y : A, n • y = x := DivisibleBy.surjective_smul A ℕ hn x
  obtain ⟨k, hk, hkx⟩ := (AddCommGroup.mem_torsion x).mp hx |>.exists_nsmul_eq_zero
  refine ⟨y, ?_, hy⟩
  exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr
    ⟨k * n, Nat.mul_pos hk (Nat.pos_of_ne_zero hn), by rw [← smul_smul, hy, hkx]⟩

/-- **Classification of divisible abelian groups.** The rational copies are indexed by a
basis of the torsion-free quotient, and the Prüfer copies at `p` by a basis of `A[p]`.
Consequently their cardinalities are intrinsic, although the resulting equivalence is a choice.
The rational structure on the quotient exists by `nonempty_ratModule` and is unique. -/
theorem nonempty_addEquiv_rat_pruferSum {A ι₀ : Type*} [AddCommGroup A] [DivisibleBy A ℕ]
    [Module ℚ (A ⧸ AddCommGroup.torsion A)] {ι : Nat.Primes → Type*}
    [∀ p : Nat.Primes, Module (ZMod p) A[(p : ℤ)]]
    (b₀ : Module.Basis ι₀ ℚ (A ⧸ AddCommGroup.torsion A))
    (b : ∀ p : Nat.Primes, Module.Basis (ι p) (ZMod p) A[(p : ℤ)]) :
    Nonempty (A ≃+ (ι₀ →₀ ℚ) × (⨁ p : Nat.Primes, (ι p →₀ prufer p))) := by
  classical
  have hD := isDivisible_torsion (A := A)
  obtain ⟨e⟩ := hD.nonempty_addEquiv_prod_quotient
  obtain ⟨_⟩ := isDivisible_iff_nonempty_divisibleBy.mp hD
  have hle (p : Nat.Primes) : A[(p : ℤ)] ≤ AddCommGroup.torsion A := by
    intro x hx
    exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr
      ⟨p, p.property.pos, torsionBy.nsmul_iff.mp hx⟩
  obtain ⟨eT⟩ := nonempty_addEquiv_torsion_pruferSum
    (A := AddCommGroup.torsion A)
    (fun x ↦ by
      obtain ⟨n, hn, hx⟩ := ((AddCommGroup.mem_torsion (x : A)).mp x.property).exists_nsmul_eq_zero
      exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, hn, Subtype.ext hx⟩)
    (fun p ↦ (b p).map (torsionBySubgroupEquiv A _ p (hle p)))
  exact ⟨e.trans ((AddEquiv.prodCongr eT b₀.repr.toAddEquiv).trans AddEquiv.prodComm)⟩

end Rational

end TauCeti
