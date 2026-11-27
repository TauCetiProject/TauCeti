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
import TauCeti.Algebra.Group.Finsupp
import TauCeti.Algebra.Module.Torsion.PrimaryComponent
import TauCeti.Algebra.Module.Torsion.Subgroup
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

/-- For prime `p`, the Prüfer subgroup of the rational circle is divisible. -/
theorem isDivisible_prufer (p : ℕ) [Fact p.Prime] : (prufer p).IsDivisible := by
  let : DivisibleBy (AddCircle (1 : ℚ)) ℕ :=
    AddGroup.divisibleByNatOfDivisibleByInt _
  exact AddCommGroup.isDivisible_primaryComponent p (Fact.out : p.Prime)

/-- The canonical embedding of the order-`p` cyclic group in the Prüfer group. -/
def pruferTorsion (p : ℕ) : ZMod p →+ prufer p where
  toFun x := ⟨ZMod.toRatAddCircle p x, 1, by
    have hx : p • ZMod.toRatAddCircle p x = 0 := by rw [← map_nsmul]; simp
    simpa using hx⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x y)

/-- The cyclic embedding agrees with the rational-circle character. -/
@[simp]
theorem coe_pruferTorsion (p : ℕ) (a : ZMod p) :
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
  -- Mathlib's primary-component theorem applies to the multiplicative presentation.
  have hprufer : IsAddPGroup p (prufer p) :=
    CommGroup.primaryComponent.isPGroup (G := Multiplicative (AddCircle (1 : ℚ)))
  refine ⟨f, hprufer.finsupp.injective_of_ker_torsionBy f ?_, hcomp⟩
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
    have htop : (⊤ : AddSubgroup (ι →₀ prufer p)).IsDivisible :=
      isDivisible_top_iff.mpr fun _ hn ↦ DivisibleBy.surjective_smul _ ℕ hn
    have h := htop.map f
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
  have hinj := hA.injective_of_ker_torsionBy r hpker
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨y, hy⟩ := (r x).property
    refine ⟨y, hinj ?_⟩
    have hy' : f y = (r x : A) := hy
    rw [hy', hr]
  exact ⟨(AddEquiv.ofBijective f ⟨hf, hsurj⟩).symm⟩

end Primary

section Torsion

open scoped DirectSum

attribute [local instance] AddSubgroup.torsionBy.zmodModule

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
      (AddCommGroup.isDivisible_primaryComponent (A := A) p p.property)
    exact nonempty_addEquiv_pruferSum
      (CommGroup.primaryComponent.isPGroup (G := Multiplicative A))
      ((b p).map ((AddCommGroup.primaryComponent A p).torsionByEquivOfLE p fun x hx ↦
        ⟨1, by simpa only [pow_one] using torsionBy.nsmul_iff.mp hx⟩))
  let e := fun p ↦ Classical.choice (hex p)
  let C := fun p : Nat.Primes ↦ (AddCommGroup.primaryComponent A p).toIntSubmodule
  let eA := (AddEquiv.ofBijective (DirectSum.coeAddMonoidHom C) hA.primaryComponent_isInternal).symm
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
  have hD := AddCommGroup.isDivisible_torsion (A := A)
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
    (fun p ↦ (b p).map ((AddCommGroup.torsion A).torsionByEquivOfLE p (hle p)))
  exact ⟨e.trans ((AddEquiv.prodCongr eT b₀.repr.toAddEquiv).trans AddEquiv.prodComm)⟩

end Rational

end TauCeti
