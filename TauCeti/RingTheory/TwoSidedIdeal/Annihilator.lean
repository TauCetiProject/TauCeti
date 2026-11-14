/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Unitization
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.TwoSidedIdeal.Kernel
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import TauCeti.Algebra.Module.Submodule.Essential

/-!
# Left and right annihilators of two-sided ideals, essential ideals, and unitization actions

In a possibly nonunital, possibly noncommutative associative ring `A`, every two-sided ideal
`I : TwoSidedIdeal A` has two two-sided annihilator ideals:
* `I.leftAnnihilator = {a : A | ∀ x ∈ I, a * x = 0}`, which absorbs multiplication on the left by
  associativity and on the right because `I` is a left ideal;
* `I.rightAnnihilator = {a : A | ∀ x ∈ I, x * a = 0}`, which absorbs multiplication on the right by
  associativity and on the left because `I` is a right ideal.

The pair `(leftAnnihilator, rightAnnihilator)` forms an antitone Galois connection on
`TwoSidedIdeal A`: `J ≤ I.leftAnnihilator ↔ I ≤ J.rightAnnihilator`, equivalently
`(J : Set A) * (I : Set A) = {0}`. Every two-sided ideal disjoint from `I` (`I ⊓ J = ⊥`) lies in
both `I.leftAnnihilator` and `I.rightAnnihilator`, so triviality of either annihilator forces `I`
to be an essential two-sided ideal (`TwoSidedIdeal.IsEssential`: `I ⊓ J ≠ ⊥` for every `J ≠ ⊥`).

When `A` is unital, `I.leftAnnihilator` coincides with `(Module.annihilator A I).toTwoSided` for
the left-multiplication module structure on `I`. When `A` is a nonunital `R`-algebra, any
`R`-submodule `L : Submodule R A` absorbing left multiplication by `A` (and any `R`-invariant
two-sided ideal `I : TwoSidedIdeal A`) carries a left `Unitization R A`-module structure
`(r, a) • x = r • x + a * x` given by multiplication inside `Unitization R A`; pulling back
`(Module.annihilator (Unitization R A) I).toTwoSided` along `Unitization.inrNonUnitalAlgHom R A`
recovers `I.leftAnnihilator`.

When `A` carries a proper involution (`IsProperStar A`) and `I` is closed under `star`, left and
right annihilation coincide (`I.leftAnnihilator = I.rightAnnihilator`), `I.leftAnnihilator` is
closed under `star`, `I ⊓ I.leftAnnihilator = ⊥`, `I ≤ I.leftAnnihilator.leftAnnihilator`, and
`I.IsEssential ↔ I.leftAnnihilator = ⊥`.

## Main definitions and results

* `Submodule.unitizationSMul` and `Submodule.unitizationModule`: the left `Unitization R A`-module
  structure `(r, a) • x = r • x + a * x` on an `R`-submodule `L : Submodule R A` absorbing left
  multiplication by `A`.
* `TwoSidedIdeal.IsEssential`: `I ⊓ J ≠ ⊥` for every nonzero `J : TwoSidedIdeal A`.
* `TwoSidedIdeal.leftAnnihilator` and `TwoSidedIdeal.rightAnnihilator`: the two-sided left and
  right annihilators of `I : TwoSidedIdeal A`, with Galois connection
  `TwoSidedIdeal.gc_leftAnnihilator_rightAnnihilator`.
* `TwoSidedIdeal.leftAnnihilator_eq_annihilator` and
  `TwoSidedIdeal.leftAnnihilator_eq_comap_unitization_of_smul_mem`: module-annihilator descriptions
  in the unital and unitized settings.
* `TwoSidedIdeal.leftAnnihilator_eq_rightAnnihilator_of_star_mem`,
  `TwoSidedIdeal.inf_leftAnnihilator_eq_bot_of_star_mem`, and
  `TwoSidedIdeal.isEssential_iff_leftAnnihilator_eq_bot_of_star_mem`: symmetry, disjointness, and
  essentiality for `star`-closed ideals in rings with proper involution.

## References

* T. Y. Lam, *Lectures on Modules and Rings*, §3D (essential submodules and annihilators).
* Bruce Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*, §II.5.4.7.
-/

public section

open scoped Pointwise

namespace Submodule

section Unitization

section NonAssocSemiring

variable {R A : Type*} [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]

/-- Left scalar action `(r, a) • x = r • x + a * x` of `Unitization R A` on an `R`-submodule
`L : Submodule R A` closed under left multiplication by `A`. Provided as a definition taking the
left-absorption hypothesis rather than a global instance. -/
@[instance_reducible]
def unitizationSMul (L : Submodule R A) (hmul : ∀ a : A, ∀ x ∈ L, a * x ∈ L) :
    SMul (Unitization R A) L where
  smul u x := ⟨u.fst • (x : A) + u.snd * (x : A),
    L.add_mem (L.smul_mem u.fst x.2) (hmul u.snd x x.2)⟩

theorem coe_unitizationSMul (L : Submodule R A) (hmul : ∀ a : A, ∀ x ∈ L, a * x ∈ L)
    (u : Unitization R A) (x : L) :
    (letI := L.unitizationSMul hmul; ((u • x : L) : A)) = u.fst • (x : A) + u.snd * (x : A) :=
  (rfl)

/-- Coercing `(r, a) • x` from `L` into `Unitization R A` agrees with multiplication in
`Unitization R A`. -/
theorem inr_coe_unitizationSMul (L : Submodule R A) (hmul : ∀ a : A, ∀ x ∈ L, a * x ∈ L)
    (u : Unitization R A) (x : L) :
    (letI := L.unitizationSMul hmul; (((u • x : L) : A) : Unitization R A)) =
      u * ((x : A) : Unitization R A) := by
  let _ := L.unitizationSMul hmul
  ext
  · simp
  · simp [coe_unitizationSMul]

end NonAssocSemiring

section Semiring

variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]

/-- Left `Unitization R A`-module structure on an `R`-submodule `L : Submodule R A` closed under
left multiplication by `A`, induced by multiplication in `Unitization R A`. -/
@[instance_reducible]
def unitizationModule (L : Submodule R A) (hmul : ∀ a : A, ∀ x ∈ L, a * x ∈ L) :
    Module (Unitization R A) L :=
  letI := L.unitizationSMul hmul
  Function.Injective.module (Unitization R A)
    ((Unitization.inrHom R R A).toAddMonoidHom.comp L.subtype.toAddMonoidHom)
    (Unitization.inr_injective.comp Subtype.coe_injective)
    (L.inr_coe_unitizationSMul hmul)

/-- Membership in `Module.annihilator (Unitization R A) L` for the unitization left action. -/
theorem mem_annihilator_unitization_iff (L : Submodule R A) (hmul : ∀ a : A, ∀ x ∈ L, a * x ∈ L)
    {u : Unitization R A} :
    (letI := L.unitizationModule hmul; u ∈ Module.annihilator (Unitization R A) L) ↔
      ∀ x ∈ L, u.fst • x + u.snd * x = 0 := by
  let _ := L.unitizationModule hmul
  rw [Module.mem_annihilator]
  refine ⟨fun h x hx => congrArg Subtype.val (h ⟨x, hx⟩), fun h x => Subtype.ext (h x x.2)⟩

end Semiring

end Unitization

end Submodule

namespace TwoSidedIdeal

section Essential

variable {A : Type*} [NonUnitalNonAssocRing A]

/-- A two-sided ideal `I` of `A` is *essential* if it has nonzero intersection with every nonzero
two-sided ideal of `A`. -/
def IsEssential (I : TwoSidedIdeal A) : Prop :=
  ∀ J : TwoSidedIdeal A, J ≠ ⊥ → I ⊓ J ≠ ⊥

theorem isEssential_def {I : TwoSidedIdeal A} :
    I.IsEssential ↔ ∀ J : TwoSidedIdeal A, J ≠ ⊥ → I ⊓ J ≠ ⊥ :=
  (Iff.rfl)

/-- Contrapositive characterization: `I` is essential iff `I ⊓ J = ⊥` forces `J = ⊥`. -/
theorem isEssential_iff_eq_bot {I : TwoSidedIdeal A} :
    I.IsEssential ↔ ∀ J : TwoSidedIdeal A, I ⊓ J = ⊥ → J = ⊥ :=
  ⟨fun h J hIJ => by_contra fun hJ => h J hJ hIJ, fun h J hJ hIJ => hJ (h J hIJ)⟩

@[simp]
theorem isEssential_top : (⊤ : TwoSidedIdeal A).IsEssential :=
  isEssential_iff_eq_bot.mpr fun J hJ => by simpa using hJ

theorem IsEssential.mono {I J : TwoSidedIdeal A} (hI : I.IsEssential) (hIJ : I ≤ J) :
    J.IsEssential :=
  isEssential_iff_eq_bot.mpr fun K hJK =>
    isEssential_iff_eq_bot.mp hI K (le_bot_iff.mp ((inf_le_inf_right K hIJ).trans hJK.le))

theorem IsEssential.inf {I J : TwoSidedIdeal A} (hI : I.IsEssential) (hJ : J.IsEssential) :
    (I ⊓ J).IsEssential :=
  isEssential_iff_eq_bot.mpr fun K hIJK =>
    isEssential_iff_eq_bot.mp hJ K <|
      isEssential_iff_eq_bot.mp hI (J ⊓ K) (by rwa [← inf_assoc])

@[simp]
theorem isEssential_inf_iff {I J : TwoSidedIdeal A} :
    (I ⊓ J).IsEssential ↔ I.IsEssential ∧ J.IsEssential :=
  ⟨fun h => ⟨h.mono inf_le_left, h.mono inf_le_right⟩, fun ⟨hI, hJ⟩ => hI.inf hJ⟩

@[simp]
theorem isEssential_bot_iff : (⊥ : TwoSidedIdeal A).IsEssential ↔ Subsingleton A := by
  rw [isEssential_iff_eq_bot]
  refine ⟨fun h => ⟨fun a b => ?_⟩, fun _ J _ => ?_⟩
  · have htop : (⊤ : TwoSidedIdeal A) = ⊥ := h ⊤ (by simp)
    have ha : a - b ∈ (⊥ : TwoSidedIdeal A) := htop ▸ mem_top A
    exact sub_eq_zero.mp ((mem_bot _).mp ha)
  · ext x
    simp [Subsingleton.elim x 0]

theorem not_isEssential_bot [Nontrivial A] : ¬ (⊥ : TwoSidedIdeal A).IsEssential := by
  rw [isEssential_bot_iff]
  exact not_subsingleton A

theorem IsEssential.ne_bot [Nontrivial A] {I : TwoSidedIdeal A} (hI : I.IsEssential) : I ≠ ⊥ :=
  fun h => not_isEssential_bot (h ▸ hI)

end Essential

section NonUnitalRing

variable {A : Type*} [NonUnitalRing A]

/-- The *left annihilator* `{a : A | ∀ x ∈ I, a * x = 0}` of a two-sided ideal `I`, bundled as a
two-sided ideal of `A`. -/
def leftAnnihilator (I : TwoSidedIdeal A) : TwoSidedIdeal A :=
  mk' {a : A | ∀ x ∈ I, a * x = 0}
    (fun x _ => zero_mul x)
    (fun {_ _} ha hb x hx => by rw [add_mul, ha x hx, hb x hx, add_zero])
    (fun {_} ha x hx => by rw [neg_mul, ha x hx, neg_zero])
    (fun {_ _} ha x hx => by rw [mul_assoc, ha x hx, mul_zero])
    -- Right absorption uses that `I` is a left ideal.
    (fun {_ r} ha x hx => by rw [mul_assoc]; exact ha (r * x) (I.mul_mem_left r x hx))

/-- The *right annihilator* `{a : A | ∀ x ∈ I, x * a = 0}` of a two-sided ideal `I`, bundled as a
two-sided ideal of `A`. -/
def rightAnnihilator (I : TwoSidedIdeal A) : TwoSidedIdeal A :=
  mk' {a : A | ∀ x ∈ I, x * a = 0}
    (fun x _ => mul_zero x)
    (fun {_ _} ha hb x hx => by rw [mul_add, ha x hx, hb x hx, add_zero])
    (fun {_} ha x hx => by rw [mul_neg, ha x hx, neg_zero])
    -- Left absorption uses that `I` is a right ideal.
    (fun {r _} ha x hx => by rw [← mul_assoc]; exact ha (x * r) (I.mul_mem_right x r hx))
    (fun {_ _} ha x hx => by rw [← mul_assoc, ha x hx, zero_mul])

@[simp]
theorem mem_leftAnnihilator {I : TwoSidedIdeal A} {a : A} :
    a ∈ I.leftAnnihilator ↔ ∀ x ∈ I, a * x = 0 :=
  mem_mk' _ _ _ _ _ _ a

theorem coe_leftAnnihilator (I : TwoSidedIdeal A) :
    (I.leftAnnihilator : Set A) = {a : A | ∀ x ∈ I, a * x = 0} :=
  Set.ext fun _ => mem_leftAnnihilator

@[simp]
theorem mem_rightAnnihilator {I : TwoSidedIdeal A} {a : A} :
    a ∈ I.rightAnnihilator ↔ ∀ x ∈ I, x * a = 0 :=
  mem_mk' _ _ _ _ _ _ a

theorem coe_rightAnnihilator (I : TwoSidedIdeal A) :
    (I.rightAnnihilator : Set A) = {a : A | ∀ x ∈ I, x * a = 0} :=
  Set.ext fun _ => mem_rightAnnihilator

theorem mul_eq_zero_of_mem_leftAnnihilator {I : TwoSidedIdeal A} {a x : A}
    (ha : a ∈ I.leftAnnihilator) (hx : x ∈ I) : a * x = 0 :=
  mem_leftAnnihilator.mp ha x hx

theorem mul_eq_zero_of_mem_rightAnnihilator {I : TwoSidedIdeal A} {a x : A}
    (hx : x ∈ I) (ha : a ∈ I.rightAnnihilator) : x * a = 0 :=
  mem_rightAnnihilator.mp ha x hx

/-- `I.leftAnnihilator` is the largest two-sided ideal `J` killing `I` on the left. -/
theorem le_leftAnnihilator_iff {I J : TwoSidedIdeal A} :
    J ≤ I.leftAnnihilator ↔ ∀ a ∈ J, ∀ x ∈ I, a * x = 0 :=
  ⟨fun h _ ha => mem_leftAnnihilator.mp (h ha), fun h _ ha => mem_leftAnnihilator.mpr (h _ ha)⟩

/-- `I.rightAnnihilator` is the largest two-sided ideal `J` killing `I` on the right. -/
theorem le_rightAnnihilator_iff {I J : TwoSidedIdeal A} :
    J ≤ I.rightAnnihilator ↔ ∀ a ∈ J, ∀ x ∈ I, x * a = 0 :=
  ⟨fun h _ ha => mem_rightAnnihilator.mp (h ha), fun h _ ha => mem_rightAnnihilator.mpr (h _ ha)⟩

/-- Pointwise set-product form of the universal property of `I.leftAnnihilator`. -/
theorem le_leftAnnihilator_iff_coe_mul_eq_singleton_zero {I J : TwoSidedIdeal A} :
    J ≤ I.leftAnnihilator ↔ (J : Set A) * (I : Set A) = {0} := by
  rw [le_leftAnnihilator_iff]
  refine ⟨fun h => Set.Subset.antisymm ?_ ?_, fun h a ha x hx => ?_⟩
  · rintro _ ⟨a, ha, x, hx, rfl⟩
    exact Set.mem_singleton_iff.mpr (h a ha x hx)
  · rw [Set.singleton_subset_iff]
    exact ⟨0, J.zero_mem, 0, I.zero_mem, mul_zero 0⟩
  · have hmem : a * x ∈ (J : Set A) * (I : Set A) := ⟨a, ha, x, hx, rfl⟩
    rwa [h, Set.mem_singleton_iff] at hmem

/-- Pointwise set-product form of the universal property of `I.rightAnnihilator`. -/
theorem le_rightAnnihilator_iff_coe_mul_eq_singleton_zero {I J : TwoSidedIdeal A} :
    J ≤ I.rightAnnihilator ↔ (I : Set A) * (J : Set A) = {0} := by
  rw [le_rightAnnihilator_iff]
  refine ⟨fun h => Set.Subset.antisymm ?_ ?_, fun h a ha x hx => ?_⟩
  · rintro _ ⟨x, hx, a, ha, rfl⟩
    exact Set.mem_singleton_iff.mpr (h a ha x hx)
  · rw [Set.singleton_subset_iff]
    exact ⟨0, I.zero_mem, 0, J.zero_mem, mul_zero 0⟩
  · have hmem : x * a ∈ (I : Set A) * (J : Set A) := ⟨x, hx, a, ha, rfl⟩
    rwa [h, Set.mem_singleton_iff] at hmem

theorem le_leftAnnihilator_iff_le_rightAnnihilator {I J : TwoSidedIdeal A} :
    J ≤ I.leftAnnihilator ↔ I ≤ J.rightAnnihilator := by
  rw [le_leftAnnihilator_iff, le_rightAnnihilator_iff]
  exact ⟨fun h x hx a ha => h a ha x hx, fun h a ha x hx => h x hx a ha⟩

/-- Antitone Galois connection between `leftAnnihilator` and `rightAnnihilator`. -/
theorem gc_leftAnnihilator_rightAnnihilator :
    GaloisConnection (OrderDual.toDual ∘ leftAnnihilator (A := A))
      (rightAnnihilator (A := A) ∘ OrderDual.ofDual) :=
  fun _ _ => le_leftAnnihilator_iff_le_rightAnnihilator

theorem leftAnnihilator_anti : Antitone (leftAnnihilator (A := A)) :=
  gc_leftAnnihilator_rightAnnihilator.monotone_l

theorem rightAnnihilator_anti : Antitone (rightAnnihilator (A := A)) :=
  fun _ _ h => gc_leftAnnihilator_rightAnnihilator.monotone_u h

theorem le_rightAnnihilator_leftAnnihilator (I : TwoSidedIdeal A) :
    I ≤ I.leftAnnihilator.rightAnnihilator :=
  le_leftAnnihilator_iff_le_rightAnnihilator.mp le_rfl

theorem le_leftAnnihilator_rightAnnihilator (I : TwoSidedIdeal A) :
    I ≤ I.rightAnnihilator.leftAnnihilator :=
  le_leftAnnihilator_iff_le_rightAnnihilator.mpr le_rfl

@[simp]
theorem leftAnnihilator_rightAnnihilator_leftAnnihilator (I : TwoSidedIdeal A) :
    I.leftAnnihilator.rightAnnihilator.leftAnnihilator = I.leftAnnihilator :=
  gc_leftAnnihilator_rightAnnihilator.l_u_l_eq_l I

@[simp]
theorem rightAnnihilator_leftAnnihilator_rightAnnihilator (I : TwoSidedIdeal A) :
    I.rightAnnihilator.leftAnnihilator.rightAnnihilator = I.rightAnnihilator :=
  gc_leftAnnihilator_rightAnnihilator.u_l_u_eq_u I

@[simp]
theorem leftAnnihilator_bot : (⊥ : TwoSidedIdeal A).leftAnnihilator = ⊤ :=
  eq_top_iff.mpr fun a _ => mem_leftAnnihilator.mpr fun x hx => by
    rw [(mem_bot _).mp hx, mul_zero]

@[simp]
theorem rightAnnihilator_bot : (⊥ : TwoSidedIdeal A).rightAnnihilator = ⊤ :=
  eq_top_iff.mpr fun a _ => mem_rightAnnihilator.mpr fun x hx => by
    rw [(mem_bot _).mp hx, zero_mul]

theorem leftAnnihilator_sup (I J : TwoSidedIdeal A) :
    (I ⊔ J).leftAnnihilator = I.leftAnnihilator ⊓ J.leftAnnihilator :=
  gc_leftAnnihilator_rightAnnihilator.l_sup

theorem rightAnnihilator_sup (I J : TwoSidedIdeal A) :
    (I ⊔ J).rightAnnihilator = I.rightAnnihilator ⊓ J.rightAnnihilator :=
  gc_leftAnnihilator_rightAnnihilator.u_inf

theorem leftAnnihilator_iSup {ι : Sort*} (I : ι → TwoSidedIdeal A) :
    (⨆ i, I i).leftAnnihilator = ⨅ i, (I i).leftAnnihilator :=
  gc_leftAnnihilator_rightAnnihilator.l_iSup

theorem rightAnnihilator_iSup {ι : Sort*} (I : ι → TwoSidedIdeal A) :
    (⨆ i, I i).rightAnnihilator = ⨅ i, (I i).rightAnnihilator :=
  gc_leftAnnihilator_rightAnnihilator.u_iInf

/-- Any two-sided ideal disjoint from `I` lies in `I.leftAnnihilator`. -/
theorem le_leftAnnihilator_of_inf_eq_bot {I J : TwoSidedIdeal A} (h : I ⊓ J = ⊥) :
    J ≤ I.leftAnnihilator :=
  -- For `a ∈ J` and `x ∈ I`, `a * x` belongs to `I ⊓ J = ⊥`.
  le_leftAnnihilator_iff.mpr fun a ha x hx =>
    (mem_bot _).mp <| h ▸ (⟨I.mul_mem_left a x hx, J.mul_mem_right a x ha⟩ : a * x ∈ I ⊓ J)

/-- Any two-sided ideal disjoint from `I` lies in `I.rightAnnihilator`. -/
theorem le_rightAnnihilator_of_inf_eq_bot {I J : TwoSidedIdeal A} (h : I ⊓ J = ⊥) :
    J ≤ I.rightAnnihilator :=
  le_rightAnnihilator_iff.mpr fun a ha x hx =>
    (mem_bot _).mp <| h ▸ (⟨I.mul_mem_right x a hx, J.mul_mem_left x a ha⟩ : x * a ∈ I ⊓ J)

/-- A two-sided ideal with trivial left annihilator is essential. -/
theorem isEssential_of_leftAnnihilator_eq_bot {I : TwoSidedIdeal A}
    (hI : I.leftAnnihilator = ⊥) : I.IsEssential :=
  isEssential_iff_eq_bot.mpr fun _ hIJ =>
    le_bot_iff.mp ((le_leftAnnihilator_of_inf_eq_bot hIJ).trans hI.le)

/-- A two-sided ideal with trivial right annihilator is essential. -/
theorem isEssential_of_rightAnnihilator_eq_bot {I : TwoSidedIdeal A}
    (hI : I.rightAnnihilator = ⊥) : I.IsEssential :=
  isEssential_iff_eq_bot.mpr fun _ hIJ =>
    le_bot_iff.mp ((le_rightAnnihilator_of_inf_eq_bot hIJ).trans hI.le)

theorem smul_mem_leftAnnihilator {M : Type*} [SMulZeroClass M A] [IsScalarTower M A A]
    (I : TwoSidedIdeal A) (c : M) {a : A} (ha : a ∈ I.leftAnnihilator) :
    c • a ∈ I.leftAnnihilator :=
  mem_leftAnnihilator.mpr fun x hx => by
    rw [smul_mul_assoc, mul_eq_zero_of_mem_leftAnnihilator ha hx, smul_zero]

theorem smul_mem_rightAnnihilator {M : Type*} [SMulZeroClass M A] [SMulCommClass M A A]
    (I : TwoSidedIdeal A) (c : M) {a : A} (ha : a ∈ I.rightAnnihilator) :
    c • a ∈ I.rightAnnihilator :=
  mem_rightAnnihilator.mpr fun x hx => by
    rw [mul_smul_comm, mul_eq_zero_of_mem_rightAnnihilator hx ha, smul_zero]

end NonUnitalRing

section Ring

variable {R : Type*} [Ring R]

/-- In a unital ring `R`, `I.leftAnnihilator` coincides with `(Module.annihilator R I).toTwoSided`
for the left-multiplication `R`-module structure on `I`. -/
theorem leftAnnihilator_eq_annihilator (I : TwoSidedIdeal R) :
    I.leftAnnihilator = (Module.annihilator R I).toTwoSided := by
  ext a
  rw [mem_leftAnnihilator, Ideal.mem_toTwoSided, Module.mem_annihilator]
  exact ⟨fun h x => Subtype.ext (h x x.2), fun h x hx => congrArg Subtype.val (h ⟨x, hx⟩)⟩

theorem asIdeal_leftAnnihilator (I : TwoSidedIdeal R) :
    I.leftAnnihilator.asIdeal = Module.annihilator R I := by
  rw [leftAnnihilator_eq_annihilator, Ideal.asIdeal_toTwoSided]

theorem le_leftAnnihilator_iff_asIdeal_mul_eq_bot {I J : TwoSidedIdeal R} :
    J ≤ I.leftAnnihilator ↔ J.asIdeal * I.asIdeal = ⊥ := by
  rw [← le_bot_iff, Ideal.mul_le, le_leftAnnihilator_iff]
  simp only [mem_asIdeal, Submodule.mem_bot]

@[simp]
theorem leftAnnihilator_top : (⊤ : TwoSidedIdeal R).leftAnnihilator = ⊥ :=
  le_bot_iff.mp fun a ha => (mem_bot _).mpr <| by
    simpa using mul_eq_zero_of_mem_leftAnnihilator ha (mem_top R (x := 1))

@[simp]
theorem rightAnnihilator_top : (⊤ : TwoSidedIdeal R).rightAnnihilator = ⊥ :=
  le_bot_iff.mp fun a ha => (mem_bot _).mpr <| by
    simpa using mul_eq_zero_of_mem_rightAnnihilator (mem_top R (x := 1)) ha

/-- If `I.asIdeal` is essential as a left ideal (`TauCeti.IsEssential`), then `I` is essential as a
two-sided ideal. -/
theorem isEssential_of_isEssential_asIdeal {I : TwoSidedIdeal R}
    (hI : TauCeti.IsEssential I.asIdeal) : I.IsEssential :=
  isEssential_iff_eq_bot.mpr fun J hIJ =>
    orderIsoIsTwoSided.injective <| Subtype.ext <|
      TauCeti.isEssential_iff.mp hI J.asIdeal (by rw [← gc.u_inf, hIJ, bot_asIdeal])

end Ring

section CommRing

/-- In a commutative ring, a two-sided ideal is essential if and only if its underlying ideal is
essential as an `R`-submodule. -/
theorem isEssential_iff_isEssential_asIdeal {R : Type*} [CommRing R] {I : TwoSidedIdeal R} :
    I.IsEssential ↔ TauCeti.IsEssential I.asIdeal :=
  ⟨fun hI => TauCeti.isEssential_iff.mpr fun K hIK => by
      have hK : Ideal.toTwoSided K = ⊥ := isEssential_iff_eq_bot.mp hI (Ideal.toTwoSided K) <|
        orderIsoIsTwoSided.injective <| Subtype.ext <| by
          simp [gc.u_inf, hIK]
      simpa using congrArg asIdeal hK,
   isEssential_of_isEssential_asIdeal⟩

end CommRing

section Unitization

section NonAssocRing

variable {R A : Type*} [Semiring R] [NonUnitalNonAssocRing A] [Module R A]

/-- Left scalar action `(r, a) • x = r • x + a * x` of `Unitization R A` on a two-sided ideal `I`
closed under `R`-scalar multiplication. Provided as a definition taking the scalar-absorption
hypothesis rather than a global instance. -/
@[instance_reducible]
def unitizationSMulOfSMulMem (I : TwoSidedIdeal A)
    (hsmul : ∀ (r : R) {x : A}, x ∈ I → r • x ∈ I) : SMul (Unitization R A) I where
  smul u x := ⟨u.fst • (x : A) + u.snd * (x : A),
    I.add_mem (hsmul u.fst x.2) (I.mul_mem_left u.snd x x.2)⟩

theorem coe_unitizationSMulOfSMulMem (I : TwoSidedIdeal A)
    (hsmul : ∀ (r : R) {x : A}, x ∈ I → r • x ∈ I) (u : Unitization R A) (x : I) :
    (letI := I.unitizationSMulOfSMulMem hsmul; ((u • x : I) : A)) =
      u.fst • (x : A) + u.snd * (x : A) :=
  (rfl)

theorem inr_coe_unitizationSMulOfSMulMem (I : TwoSidedIdeal A)
    (hsmul : ∀ (r : R) {x : A}, x ∈ I → r • x ∈ I) (u : Unitization R A) (x : I) :
    (letI := I.unitizationSMulOfSMulMem hsmul; (((u • x : I) : A) : Unitization R A)) =
      u * ((x : A) : Unitization R A) := by
  let _ := I.unitizationSMulOfSMulMem hsmul
  ext
  · simp
  · simp [coe_unitizationSMulOfSMulMem]

end NonAssocRing

section CommSemiring

variable {R A : Type*} [CommSemiring R] [NonUnitalRing A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]

/-- Left `Unitization R A`-module structure `(r, a) • x = r • x + a * x` on an `R`-invariant
two-sided ideal `I : TwoSidedIdeal A`. -/
@[instance_reducible]
def unitizationModuleOfSMulMem (I : TwoSidedIdeal A)
    (hsmul : ∀ (r : R) {x : A}, x ∈ I → r • x ∈ I) : Module (Unitization R A) I :=
  letI := I.unitizationSMulOfSMulMem hsmul
  Function.Injective.module (Unitization R A)
    ((Unitization.inrHom R R A).toAddMonoidHom.comp I.coeAddMonoidHom)
    (Unitization.inr_injective.comp Subtype.coe_injective)
    (I.inr_coe_unitizationSMulOfSMulMem hsmul)

theorem mem_annihilator_unitizationOfSMulMem_iff (I : TwoSidedIdeal A)
    (hsmul : ∀ (r : R) {x : A}, x ∈ I → r • x ∈ I) {u : Unitization R A} :
    (letI := I.unitizationModuleOfSMulMem hsmul; u ∈ Module.annihilator (Unitization R A) I) ↔
      ∀ x ∈ I, u.fst • x + u.snd * x = 0 := by
  let _ := I.unitizationModuleOfSMulMem hsmul
  rw [Module.mem_annihilator]
  refine ⟨fun h x hx => congrArg Subtype.val (h ⟨x, hx⟩), fun h x => Subtype.ext (h x x.2)⟩

end CommSemiring

/-- For an `R`-invariant two-sided ideal `I` of a nonunital `R`-algebra `A`, `I.leftAnnihilator` is
the preimage of `(Module.annihilator (Unitization R A) I).toTwoSided` under
`Unitization.inrNonUnitalAlgHom R A`. -/
theorem leftAnnihilator_eq_comap_unitization_of_smul_mem {R A : Type*} [CommRing R]
    [NonUnitalRing A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    (I : TwoSidedIdeal A) (hsmul : ∀ (r : R) {x : A}, x ∈ I → r • x ∈ I) :
    letI := I.unitizationModuleOfSMulMem hsmul
    I.leftAnnihilator =
      TwoSidedIdeal.comap (Unitization.inrNonUnitalAlgHom R A)
        (Module.annihilator (Unitization R A) I).toTwoSided := by
  let _ := I.unitizationModuleOfSMulMem hsmul
  ext a
  rw [mem_leftAnnihilator, mem_comap, Ideal.mem_toTwoSided,
    I.mem_annihilator_unitizationOfSMulMem_iff hsmul]
  simp

end Unitization

section ProperStar

variable {A : Type*} [NonUnitalRing A] [StarRing A] [IsProperStar A]

@[simp]
theorem leftAnnihilator_top_of_isProperStar : (⊤ : TwoSidedIdeal A).leftAnnihilator = ⊥ :=
  le_bot_iff.mp fun _ ha => (mem_bot _).mpr <|
    mul_star_self_eq_zero.mp (mul_eq_zero_of_mem_leftAnnihilator ha (mem_top A))

@[simp]
theorem rightAnnihilator_top_of_isProperStar : (⊤ : TwoSidedIdeal A).rightAnnihilator = ⊥ :=
  le_bot_iff.mp fun _ ha => (mem_bot _).mpr <|
    star_mul_self_eq_zero.mp (mul_eq_zero_of_mem_rightAnnihilator (mem_top A) ha)

/-- For a `star`-closed two-sided ideal `I` in a ring with proper involution, the left and right
annihilators of `I` coincide. -/
theorem leftAnnihilator_eq_rightAnnihilator_of_star_mem {I : TwoSidedIdeal A}
    (hstar : ∀ {x : A}, x ∈ I → star x ∈ I) :
    I.leftAnnihilator = I.rightAnnihilator := by
  ext a
  rw [mem_leftAnnihilator, mem_rightAnnihilator]
  refine ⟨fun ha x hx => ?_, fun ha x hx => ?_⟩
  · -- Since `star (x * a) ∈ I`, `(x * a) * star (x * a) = x * (a * star (x * a)) = 0`.
    refine mul_star_self_eq_zero.mp ?_
    rw [mul_assoc, ha (star (x * a)) (hstar (I.mul_mem_right x a hx)), mul_zero]
  · refine star_mul_self_eq_zero.mp ?_
    rw [← mul_assoc, ha (star (a * x)) (hstar (I.mul_mem_left a x hx)), zero_mul]

theorem mem_leftAnnihilator_iff_mul_right_of_star_mem {I : TwoSidedIdeal A}
    (hstar : ∀ {x : A}, x ∈ I → star x ∈ I) {a : A} :
    a ∈ I.leftAnnihilator ↔ ∀ x ∈ I, x * a = 0 := by
  rw [leftAnnihilator_eq_rightAnnihilator_of_star_mem hstar, mem_rightAnnihilator]

theorem star_mem_leftAnnihilator_of_star_mem {I : TwoSidedIdeal A}
    (hstar : ∀ {x : A}, x ∈ I → star x ∈ I) {a : A} (ha : a ∈ I.leftAnnihilator) :
    star a ∈ I.leftAnnihilator :=
  mem_leftAnnihilator.mpr fun x hx => by
    have hxa : star x * a = 0 :=
      (mem_leftAnnihilator_iff_mul_right_of_star_mem hstar).mp ha (star x) (hstar hx)
    simpa using congrArg star hxa

theorem star_mem_rightAnnihilator_of_star_mem {I : TwoSidedIdeal A}
    (hstar : ∀ {x : A}, x ∈ I → star x ∈ I) {a : A} (ha : a ∈ I.rightAnnihilator) :
    star a ∈ I.rightAnnihilator := by
  rw [← leftAnnihilator_eq_rightAnnihilator_of_star_mem hstar] at ha ⊢
  exact star_mem_leftAnnihilator_of_star_mem hstar ha

theorem star_mem_leftAnnihilator_iff_of_star_mem {I : TwoSidedIdeal A}
    (hstar : ∀ {x : A}, x ∈ I → star x ∈ I) {a : A} :
    star a ∈ I.leftAnnihilator ↔ a ∈ I.leftAnnihilator :=
  ⟨fun h => star_star a ▸ star_mem_leftAnnihilator_of_star_mem hstar h,
   star_mem_leftAnnihilator_of_star_mem hstar⟩

/-- In a ring with proper involution, a `star`-closed two-sided ideal meets its annihilator
trivially. -/
theorem inf_leftAnnihilator_eq_bot_of_star_mem {I : TwoSidedIdeal A}
    (hstar : ∀ {x : A}, x ∈ I → star x ∈ I) :
    I ⊓ I.leftAnnihilator = ⊥ :=
  -- For `a ∈ I ⊓ I.leftAnnihilator`, `star a ∈ I` gives `a * star a = 0`, hence `a = 0`.
  le_bot_iff.mp fun _ ha => (mem_bot _).mpr <|
    mul_star_self_eq_zero.mp (mul_eq_zero_of_mem_leftAnnihilator ha.2 (hstar ha.1))

theorem leftAnnihilator_inf_eq_bot_of_star_mem {I : TwoSidedIdeal A}
    (hstar : ∀ {x : A}, x ∈ I → star x ∈ I) :
    I.leftAnnihilator ⊓ I = ⊥ := by
  rw [inf_comm]
  exact inf_leftAnnihilator_eq_bot_of_star_mem hstar

theorem le_leftAnnihilator_leftAnnihilator_of_star_mem {I : TwoSidedIdeal A}
    (hstar : ∀ {x : A}, x ∈ I → star x ∈ I) :
    I ≤ I.leftAnnihilator.leftAnnihilator := by
  rw [leftAnnihilator_eq_rightAnnihilator_of_star_mem (star_mem_leftAnnihilator_of_star_mem hstar)]
  exact I.le_rightAnnihilator_leftAnnihilator

theorem leftAnnihilator_leftAnnihilator_leftAnnihilator_of_star_mem {I : TwoSidedIdeal A}
    (hstar : ∀ {x : A}, x ∈ I → star x ∈ I) :
    I.leftAnnihilator.leftAnnihilator.leftAnnihilator = I.leftAnnihilator :=
  le_antisymm
    (leftAnnihilator_anti (le_leftAnnihilator_leftAnnihilator_of_star_mem hstar))
    (le_leftAnnihilator_leftAnnihilator_of_star_mem (star_mem_leftAnnihilator_of_star_mem hstar))

theorem le_leftAnnihilator_iff_inf_eq_bot_of_star_mem {I J : TwoSidedIdeal A}
    (hstar : ∀ {x : A}, x ∈ I → star x ∈ I) :
    J ≤ I.leftAnnihilator ↔ I ⊓ J = ⊥ :=
  ⟨fun h => le_bot_iff.mp ((inf_le_inf_left I h).trans
      (inf_leftAnnihilator_eq_bot_of_star_mem hstar).le),
   le_leftAnnihilator_of_inf_eq_bot⟩

/-- A `star`-closed two-sided ideal in a ring with proper involution is essential if and only if
its left annihilator is trivial. -/
theorem isEssential_iff_leftAnnihilator_eq_bot_of_star_mem {I : TwoSidedIdeal A}
    (hstar : ∀ {x : A}, x ∈ I → star x ∈ I) :
    I.IsEssential ↔ I.leftAnnihilator = ⊥ :=
  ⟨fun h => isEssential_iff_eq_bot.mp h I.leftAnnihilator
      (inf_leftAnnihilator_eq_bot_of_star_mem hstar),
   isEssential_of_leftAnnihilator_eq_bot⟩

theorem isEssential_iff_rightAnnihilator_eq_bot_of_star_mem {I : TwoSidedIdeal A}
    (hstar : ∀ {x : A}, x ∈ I → star x ∈ I) :
    I.IsEssential ↔ I.rightAnnihilator = ⊥ := by
  rw [isEssential_iff_leftAnnihilator_eq_bot_of_star_mem hstar,
    leftAnnihilator_eq_rightAnnihilator_of_star_mem hstar]

end ProperStar

section Prod

/-- In a product `A × B`, the first-factor ideal `A × {0} = ker snd` is essential if and only if `B`
is a subsingleton. -/
@[simp]
theorem isEssential_ker_snd_iff {A B : Type*} [NonUnitalNonAssocRing A]
    [NonUnitalNonAssocRing B] :
    (TwoSidedIdeal.ker (NonUnitalRingHom.snd A B)).IsEssential ↔ Subsingleton B := by
  rw [isEssential_iff_eq_bot]
  refine ⟨fun h => ⟨fun b₁ b₂ => ?_⟩, fun _ J hJ => ?_⟩
  · have hinf : TwoSidedIdeal.ker (NonUnitalRingHom.snd A B) ⊓
        TwoSidedIdeal.ker (NonUnitalRingHom.fst A B) = ⊥ := by
      ext p
      simp [mem_inf, mem_ker, Prod.ext_iff, and_comm]
    have hbot := h _ hinf
    have hmem : ((0 : A), b₁ - b₂) ∈ (⊥ : TwoSidedIdeal (A × B)) :=
      hbot ▸ (mem_ker _).mpr rfl
    exact sub_eq_zero.mp (congrArg Prod.snd ((mem_bot _).mp hmem))
  · have htop : TwoSidedIdeal.ker (NonUnitalRingHom.snd A B) = ⊤ := by
      ext p
      simp [mem_ker, Subsingleton.elim p.2 0]
    simpa [htop] using hJ

/-- In a product `A × B`, the second-factor ideal `{0} × B = ker fst` is essential if and only if
`A` is a subsingleton. -/
@[simp]
theorem isEssential_ker_fst_iff {A B : Type*} [NonUnitalNonAssocRing A]
    [NonUnitalNonAssocRing B] :
    (TwoSidedIdeal.ker (NonUnitalRingHom.fst A B)).IsEssential ↔ Subsingleton A := by
  rw [isEssential_iff_eq_bot]
  refine ⟨fun h => ⟨fun a₁ a₂ => ?_⟩, fun _ J hJ => ?_⟩
  · have hinf : TwoSidedIdeal.ker (NonUnitalRingHom.fst A B) ⊓
        TwoSidedIdeal.ker (NonUnitalRingHom.snd A B) = ⊥ := by
      ext p
      simp [mem_inf, mem_ker, Prod.ext_iff]
    have hbot := h _ hinf
    have hmem : (a₁ - a₂, (0 : B)) ∈ (⊥ : TwoSidedIdeal (A × B)) :=
      hbot ▸ (mem_ker _).mpr rfl
    exact sub_eq_zero.mp (congrArg Prod.fst ((mem_bot _).mp hmem))
  · have htop : TwoSidedIdeal.ker (NonUnitalRingHom.fst A B) = ⊤ := by
      ext p
      simp [mem_ker, Subsingleton.elim p.1 0]
    simpa [htop] using hJ

/-- In a product `A × B` of nonunital rings, the left annihilator of `ker snd = A × {0}` is the
preimage of `(⊤ : TwoSidedIdeal A).leftAnnihilator` along `fst`. -/
theorem leftAnnihilator_ker_snd_eq_comap {A B : Type*} [NonUnitalRing A] [NonUnitalRing B] :
    (TwoSidedIdeal.ker (NonUnitalRingHom.snd A B)).leftAnnihilator =
      (⊤ : TwoSidedIdeal A).leftAnnihilator.comap (NonUnitalRingHom.fst A B) := by
  ext p
  rw [mem_leftAnnihilator, mem_comap, mem_leftAnnihilator]
  refine ⟨fun h a _ => congrArg Prod.fst (h (a, 0) ((mem_ker _).mpr rfl)), fun h x hx => ?_⟩
  have hx2 : x.2 = 0 := (mem_ker _).mp hx
  ext
  · exact h x.1 (mem_top A)
  · simp [hx2]

theorem rightAnnihilator_ker_snd_eq_comap {A B : Type*} [NonUnitalRing A] [NonUnitalRing B] :
    (TwoSidedIdeal.ker (NonUnitalRingHom.snd A B)).rightAnnihilator =
      (⊤ : TwoSidedIdeal A).rightAnnihilator.comap (NonUnitalRingHom.fst A B) := by
  ext p
  rw [mem_rightAnnihilator, mem_comap, mem_rightAnnihilator]
  refine ⟨fun h a _ => congrArg Prod.fst (h (a, 0) ((mem_ker _).mpr rfl)), fun h x hx => ?_⟩
  have hx2 : x.2 = 0 := (mem_ker _).mp hx
  ext
  · exact h x.1 (mem_top A)
  · simp [hx2]

/-- In a product `A × B` of nonunital rings, the left annihilator of `ker fst = {0} × B` is the
preimage of `(⊤ : TwoSidedIdeal B).leftAnnihilator` along `snd`. -/
theorem leftAnnihilator_ker_fst_eq_comap {A B : Type*} [NonUnitalRing A] [NonUnitalRing B] :
    (TwoSidedIdeal.ker (NonUnitalRingHom.fst A B)).leftAnnihilator =
      (⊤ : TwoSidedIdeal B).leftAnnihilator.comap (NonUnitalRingHom.snd A B) := by
  ext p
  rw [mem_leftAnnihilator, mem_comap, mem_leftAnnihilator]
  refine ⟨fun h b _ => congrArg Prod.snd (h (0, b) ((mem_ker _).mpr rfl)), fun h x hx => ?_⟩
  have hx1 : x.1 = 0 := (mem_ker _).mp hx
  ext
  · simp [hx1]
  · exact h x.2 (mem_top B)

theorem rightAnnihilator_ker_fst_eq_comap {A B : Type*} [NonUnitalRing A] [NonUnitalRing B] :
    (TwoSidedIdeal.ker (NonUnitalRingHom.fst A B)).rightAnnihilator =
      (⊤ : TwoSidedIdeal B).rightAnnihilator.comap (NonUnitalRingHom.snd A B) := by
  ext p
  rw [mem_rightAnnihilator, mem_comap, mem_rightAnnihilator]
  refine ⟨fun h b _ => congrArg Prod.snd (h (0, b) ((mem_ker _).mpr rfl)), fun h x hx => ?_⟩
  have hx1 : x.1 = 0 := (mem_ker _).mp hx
  ext
  · simp [hx1]
  · exact h x.2 (mem_top B)

theorem leftAnnihilator_ker_snd_of_ring {A B : Type*} [Ring A] [NonUnitalRing B] :
    (TwoSidedIdeal.ker (NonUnitalRingHom.snd A B)).leftAnnihilator =
      TwoSidedIdeal.ker (NonUnitalRingHom.fst A B) := by
  ext p
  simp [leftAnnihilator_ker_snd_eq_comap, mem_comap, mem_ker]

theorem leftAnnihilator_ker_fst_of_ring {A B : Type*} [NonUnitalRing A] [Ring B] :
    (TwoSidedIdeal.ker (NonUnitalRingHom.fst A B)).leftAnnihilator =
      TwoSidedIdeal.ker (NonUnitalRingHom.snd A B) := by
  ext p
  simp [leftAnnihilator_ker_fst_eq_comap, mem_comap, mem_ker]

/-- In a product `A × B` whose first factor has a proper involution, the left annihilator of the
first-factor ideal `A × {0} = ker snd` is the second-factor ideal `{0} × B = ker fst`. -/
theorem leftAnnihilator_ker_snd {A B : Type*} [NonUnitalRing A] [StarRing A] [IsProperStar A]
    [NonUnitalRing B] :
    (TwoSidedIdeal.ker (NonUnitalRingHom.snd A B)).leftAnnihilator =
      TwoSidedIdeal.ker (NonUnitalRingHom.fst A B) := by
  ext p
  simp [leftAnnihilator_ker_snd_eq_comap, mem_comap, mem_ker]

/-- In a product `A × B` whose second factor has a proper involution, the left annihilator of the
second-factor ideal `{0} × B = ker fst` is the first-factor ideal `A × {0} = ker snd`. -/
theorem leftAnnihilator_ker_fst {A B : Type*} [NonUnitalRing A]
    [NonUnitalRing B] [StarRing B] [IsProperStar B] :
    (TwoSidedIdeal.ker (NonUnitalRingHom.fst A B)).leftAnnihilator =
      TwoSidedIdeal.ker (NonUnitalRingHom.snd A B) := by
  ext p
  simp [leftAnnihilator_ker_fst_eq_comap, mem_comap, mem_ker]

end Prod

end TwoSidedIdeal
