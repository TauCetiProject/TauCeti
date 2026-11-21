/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Hom
public import TauCeti.Analysis.CStarAlgebra.Ideal
public import TauCeti.Analysis.CStarAlgebra.Multiplier.Basic
public import TauCeti.RingTheory.TwoSidedIdeal.Annihilator

/-!
# Annihilators and essential ideals in C⋆-algebras

In a possibly nonunital C⋆-algebra `A`, every closed two-sided ideal is closed under `star`
(`TwoSidedIdeal.star_mem_of_isClosed`), and taking topological closure does not change the left or
right annihilator (`TwoSidedIdeal.annihilator_topologicalClosure`). Combining these with the
properness of the involution yields the full C⋆-algebra annihilator theory for *all* two-sided
ideals `I : TwoSidedIdeal A` (closed or not):
* `I.annihilator` is a closed two-sided ideal of `A`, hence a nonunital C⋆-algebra in its own right;
* left and right annihilation coincide (`I.annihilator = I.rightAnnihilator`);
* `I` meets its annihilator trivially (`I ⊓ I.annihilator = ⊥`), `I.topologicalClosure ≤
  I.annihilator.annihilator`, and `I.annihilator.annihilator.annihilator = I.annihilator`;
* essentiality among closed ideals, algebraic essentiality, and triviality of the annihilator are
  all equivalent (`I.IsClosedEssential ↔ I.IsEssential ↔ I.annihilator = ⊥`).

In the unital case `[CStarAlgebra A]`, `I.annihilator` agrees with
`(Module.annihilator A I).toTwoSided`, and `star`-invariance transfers directly to
`Module.annihilator A I` and its two-sided bundling.

In the nonunital case `[NonUnitalCStarAlgebra A]`, a closed two-sided ideal `I` absorbs complex
scalars (`TwoSidedIdeal.smul_mem_of_isClosed`), hence carries the left `Unitization ℂ A`-module
action `(z, a) • x = z • x + a * x` (`TwoSidedIdeal.unitizationModule`, provided as an
`@[instance_reducible]` definition rather than a global instance). Under this action,
`I.annihilator` is the preimage in `A` of `(Module.annihilator (Unitization ℂ A) I).toTwoSided`
along `Unitization.inrNonUnitalAlgHom ℂ A`
(`TwoSidedIdeal.annihilator_eq_comap_toTwoSided_annihilator`), extending
`TwoSidedIdeal.annihilator_eq_toTwoSided_annihilator` from the unital case and making this pullback
closed and closed under complex scalars and `star`.

Finally, for any closed two-sided ideal `I`, the canonical homomorphism
`A →⋆ₙₐ[ℂ] 𝓜(ℂ, I.toNonUnitalStarSubalgebra)` (and its transport
`I.multiplierHom : A →⋆ₙₐ[ℂ] 𝓜(ℂ, I)`) into the multiplier algebra of `I` has kernel
`I.annihilator`, so it is injective (and hence isometric) precisely when `I` is essential.

## Main declarations

* `TwoSidedIdeal.annihilator_eq_rightAnnihilator`, `TwoSidedIdeal.inf_annihilator_eq_bot`,
  `TwoSidedIdeal.topologicalClosure_le_annihilator_annihilator`, and
  `TwoSidedIdeal.isClosedEssential_iff_annihilator_eq_bot`: symmetry, disjointness, double
  annihilator inclusion, and essentiality in any `NonUnitalCStarAlgebra`.
* `TwoSidedIdeal.star_mem_moduleAnnihilator_toTwoSided` and
  `TwoSidedIdeal.star_mem_moduleAnnihilator`: `star`-invariance of
  `(Module.annihilator A I).toTwoSided` and `Module.annihilator A I` in unital C⋆-algebras.
* `TwoSidedIdeal.unitizationModule`, `TwoSidedIdeal.coe_unitizationModule_smul`,
  `TwoSidedIdeal.isScalarTower_unitizationModule`, and
  `TwoSidedIdeal.annihilator_eq_comap_toTwoSided_annihilator`: left `Unitization ℂ A`-module
  action on a closed ideal `I` and identification of `I.annihilator` with the pullback of
  `Module.annihilator (Unitization ℂ A) I`.
* `TwoSidedIdeal.ker_multiplierHom`, `TwoSidedIdeal.multiplierHom_injective_iff_isEssential`,
  `TwoSidedIdeal.multiplierHom`, and `TwoSidedIdeal.IsClosedEssential.isometry_multiplierHom`:
  the canonical multiplier homomorphisms and their kernel, injectivity, and isometry
  characterizations.

## References

* B. Blackadar, *Operator Algebras*, II.5.4 and II.7.3.
* G. J. Murphy, *C⋆-Algebras and Operator Theory*, Section 3.1.
* Iain Raeburn and Dana Williams, *Morita Equivalence and Continuous-Trace C*-Algebras*,
  Proposition 2.54.
-/

public section

open scoped CStarAlgebra MultiplierAlgebra

namespace TwoSidedIdeal

section NonUnitalCStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- A closed two-sided ideal of a C⋆-algebra is essential exactly when its annihilator vanishes. -/
theorem annihilator_eq_bot_iff_isEssential_of_isClosed (I : TwoSidedIdeal A)
    [IsClosed (I : Set A)] : I.annihilator = ⊥ ↔ I.IsEssential :=
  annihilator_eq_bot_iff_isEssential fun _ ↦ I.star_mem_of_isClosed

/-- In any C⋆-algebra, the left and right annihilators of a two-sided ideal `I` coincide. -/
theorem annihilator_eq_rightAnnihilator (I : TwoSidedIdeal A) :
    I.annihilator = I.rightAnnihilator := by
  -- Passing to `I.topologicalClosure` preserves both annihilators and yields a `star`-closed ideal.
  have _ : IsClosed (I.topologicalClosure : Set A) := I.isClosed_topologicalClosure
  rw [← I.annihilator_topologicalClosure, ← I.rightAnnihilator_topologicalClosure]
  exact annihilator_eq_rightAnnihilator_of_star_mem
    fun _ => I.topologicalClosure.star_mem_of_isClosed

theorem mem_annihilator_iff_mul_eq_zero_right {I : TwoSidedIdeal A} {a : A} :
    a ∈ I.annihilator ↔ ∀ x ∈ I, x * a = 0 := by
  rw [I.annihilator_eq_rightAnnihilator, mem_rightAnnihilator]

/-- The annihilator of any two-sided ideal in a C⋆-algebra is closed under `star`. -/
theorem star_mem_annihilator_of_cstar {I : TwoSidedIdeal A} {a : A} (ha : a ∈ I.annihilator) :
    star a ∈ I.annihilator :=
  I.annihilator.star_mem_of_isClosed ha

/-- The right annihilator of any two-sided ideal in a C⋆-algebra is closed under `star`. -/
theorem star_mem_rightAnnihilator {I : TwoSidedIdeal A} {a : A} (ha : a ∈ I.rightAnnihilator) :
    star a ∈ I.rightAnnihilator :=
  I.rightAnnihilator.star_mem_of_isClosed ha

/-- Every two-sided ideal of a C⋆-algebra has trivial intersection with its annihilator. -/
@[simp]
theorem inf_annihilator_eq_bot (I : TwoSidedIdeal A) : I ⊓ I.annihilator = ⊥ := by
  have _ : IsClosed (I.topologicalClosure : Set A) := I.isClosed_topologicalClosure
  refine le_bot_iff.mp ((inf_le_inf_right I.annihilator I.le_topologicalClosure).trans ?_)
  rw [← I.annihilator_topologicalClosure,
    inf_annihilator fun _ => I.topologicalClosure.star_mem_of_isClosed]

@[simp]
theorem annihilator_inf_eq_bot (I : TwoSidedIdeal A) : I.annihilator ⊓ I = ⊥ := by
  rw [inf_comm, I.inf_annihilator_eq_bot]

@[simp]
theorem inf_rightAnnihilator_eq_bot (I : TwoSidedIdeal A) : I ⊓ I.rightAnnihilator = ⊥ := by
  rw [← I.annihilator_eq_rightAnnihilator, I.inf_annihilator_eq_bot]

@[simp]
theorem rightAnnihilator_inf_eq_bot (I : TwoSidedIdeal A) : I.rightAnnihilator ⊓ I = ⊥ := by
  rw [inf_comm, I.inf_rightAnnihilator_eq_bot]

theorem coe_inter_annihilator_eq_singleton_zero (I : TwoSidedIdeal A) :
    (I : Set A) ∩ (I.annihilator : Set A) = {0} := by
  calc (I : Set A) ∩ (I.annihilator : Set A)
      = ((I ⊓ I.annihilator : TwoSidedIdeal A) : Set A) := rfl
    _ = ((⊥ : TwoSidedIdeal A) : Set A) := by rw [I.inf_annihilator_eq_bot]
    _ = {0} := coe_bot A

/-- The topological closure of `I` is contained in its double annihilator. -/
theorem topologicalClosure_le_annihilator_annihilator (I : TwoSidedIdeal A) :
    I.topologicalClosure ≤ I.annihilator.annihilator := by
  have _ : IsClosed (I.topologicalClosure : Set A) := I.isClosed_topologicalClosure
  simpa only [I.annihilator_topologicalClosure] using
    le_annihilator_annihilator fun _ => I.topologicalClosure.star_mem_of_isClosed

theorem le_annihilator_annihilator_of_cstar (I : TwoSidedIdeal A) :
    I ≤ I.annihilator.annihilator :=
  I.le_topologicalClosure.trans I.topologicalClosure_le_annihilator_annihilator

@[simp]
theorem annihilator_annihilator_annihilator_of_cstar (I : TwoSidedIdeal A) :
    I.annihilator.annihilator.annihilator = I.annihilator :=
  le_antisymm
    (annihilator_le_annihilator I.le_annihilator_annihilator_of_cstar)
    I.annihilator.le_annihilator_annihilator_of_cstar

/-- In a C⋆-algebra, a two-sided ideal `J` annihilates `I` if and only if `I ⊓ J = ⊥`. -/
theorem le_annihilator_iff_inf_eq_bot {I J : TwoSidedIdeal A} :
    J ≤ I.annihilator ↔ I ⊓ J = ⊥ :=
  ⟨fun h => le_bot_iff.mp ((inf_le_inf_left I h).trans I.inf_annihilator_eq_bot.le),
   le_annihilator_of_inf_eq_bot⟩

/-- A two-sided ideal of a C⋆-algebra is essential among closed ideals if and only if its left
annihilator is `⊥`. -/
theorem isClosedEssential_iff_annihilator_eq_bot {I : TwoSidedIdeal A} :
    I.IsClosedEssential ↔ I.annihilator = ⊥ :=
  ⟨fun h => isClosedEssential_iff.mp h I.annihilator I.isClosed_annihilator
      I.inf_annihilator_eq_bot,
   isClosedEssential_of_annihilator_eq_bot⟩

theorem isClosedEssential_iff_rightAnnihilator_eq_bot {I : TwoSidedIdeal A} :
    I.IsClosedEssential ↔ I.rightAnnihilator = ⊥ := by
  rw [isClosedEssential_iff_annihilator_eq_bot, I.annihilator_eq_rightAnnihilator]

/-- In a C⋆-algebra, essentiality among closed two-sided ideals and algebraic essentiality among all
two-sided ideals are equivalent. -/
theorem isClosedEssential_iff_isEssential {I : TwoSidedIdeal A} :
    I.IsClosedEssential ↔ I.IsEssential :=
  ⟨fun h => isEssential_of_annihilator_eq_bot
      (isClosedEssential_iff_annihilator_eq_bot.mp h),
   IsEssential.isClosedEssential⟩

theorem isEssential_iff_annihilator_eq_bot {I : TwoSidedIdeal A} :
    I.IsEssential ↔ I.annihilator = ⊥ := by
  rw [← isClosedEssential_iff_isEssential, isClosedEssential_iff_annihilator_eq_bot]

theorem isEssential_iff_rightAnnihilator_eq_bot {I : TwoSidedIdeal A} :
    I.IsEssential ↔ I.rightAnnihilator = ⊥ := by
  rw [isEssential_iff_annihilator_eq_bot, I.annihilator_eq_rightAnnihilator]

theorem IsClosedEssential.inf {I J : TwoSidedIdeal A}
    (hI : I.IsClosedEssential) (hJ : J.IsClosedEssential) : (I ⊓ J).IsClosedEssential :=
  isClosedEssential_iff_isEssential.mpr
    ((isClosedEssential_iff_isEssential.mp hI).inf (isClosedEssential_iff_isEssential.mp hJ))

@[simp]
theorem isClosedEssential_inf_iff {I J : TwoSidedIdeal A} :
    (I ⊓ J).IsClosedEssential ↔ I.IsClosedEssential ∧ J.IsClosedEssential :=
  ⟨fun h => ⟨h.mono inf_le_left, h.mono inf_le_right⟩, fun ⟨hI, hJ⟩ => hI.inf hJ⟩

@[simp]
theorem isClosedEssential_topologicalClosure_iff {I : TwoSidedIdeal A} :
    I.topologicalClosure.IsClosedEssential ↔ I.IsClosedEssential := by
  rw [isClosedEssential_iff_annihilator_eq_bot, isClosedEssential_iff_annihilator_eq_bot,
    I.annihilator_topologicalClosure]

@[simp]
theorem isEssential_topologicalClosure_iff {I : TwoSidedIdeal A} :
    I.topologicalClosure.IsEssential ↔ I.IsEssential := by
  rw [← isClosedEssential_iff_isEssential, ← isClosedEssential_iff_isEssential,
    isClosedEssential_topologicalClosure_iff]

/-- Pulling back along a ring equivalence between C⋆-algebras preserves and reflects
closed-essentiality. -/
@[simp]
theorem isClosedEssential_comap_iff {B E : Type*} [NonUnitalCStarAlgebra B]
    [EquivLike E A B] [NonUnitalRingHomClass E A B] (e : E) {I : TwoSidedIdeal B} :
    (I.comap e).IsClosedEssential ↔ I.IsClosedEssential := by
  rw [isClosedEssential_iff_isEssential, isClosedEssential_iff_isEssential, isEssential_comap_iff]

end NonUnitalCStarAlgebra

section UnitalCStarAlgebra

variable {A : Type*} [CStarAlgebra A]

/-- For any two-sided ideal `I` of a unital C⋆-algebra `A`, `(Module.annihilator A I).toTwoSided` is
closed under `star`. -/
theorem star_mem_moduleAnnihilator_toTwoSided {I : TwoSidedIdeal A} {a : A}
    (ha : a ∈ (Module.annihilator A I).toTwoSided) :
    star a ∈ (Module.annihilator A I).toTwoSided := by
  rw [← annihilator_eq_moduleAnnihilator_toTwoSided] at ha ⊢
  exact star_mem_annihilator_of_cstar ha

/-- For any two-sided ideal `I` of a unital C⋆-algebra `A`, `Module.annihilator A I` is closed under
`star`. -/
theorem star_mem_moduleAnnihilator {I : TwoSidedIdeal A} {a : A}
    (ha : a ∈ Module.annihilator A I) : star a ∈ Module.annihilator A I :=
  Ideal.mem_toTwoSided.mp
    (star_mem_moduleAnnihilator_toTwoSided (Ideal.mem_toTwoSided.mpr ha))

end UnitalCStarAlgebra

section Unitization

variable {A : Type*} [NonUnitalCStarAlgebra A] (I : TwoSidedIdeal A) [IsClosed (I : Set A)]

/-- Left multiplication by elements of `A` on a closed two-sided ideal `I`, as a nonunital algebra
homomorphism into the complex-linear endomorphisms of `I`. -/
def mulLeftEnd : A →ₙₐ[ℂ] Module.End ℂ I where
  toFun a :=
    { toFun x := ⟨a * x, I.mul_mem_left a x x.property⟩
      map_add' x y := Subtype.ext (mul_add a (x : A) y)
      map_smul' c x := Subtype.ext (mul_smul_comm c a (x : A)) }
  map_smul' c a := LinearMap.ext fun x ↦ Subtype.ext (smul_mul_assoc c a (x : A))
  map_zero' := LinearMap.ext fun x ↦ Subtype.ext (zero_mul (x : A))
  map_add' a b := LinearMap.ext fun x ↦ Subtype.ext (add_mul a b (x : A))
  map_mul' a b := LinearMap.ext fun x ↦ Subtype.ext (mul_assoc a b (x : A))

@[simp]
theorem coe_mulLeftEnd_apply (a : A) (x : I) : ((I.mulLeftEnd a x : I) : A) = a * x :=
  (rfl)

/-- The left action `(z, a) • x = z • x + a * x` of the unitization `Unitization ℂ A` on a closed
two-sided ideal `I`. -/
@[instance_reducible]
noncomputable def unitizationModule : Module (Unitization ℂ A) I :=
  Module.compHom I (Unitization.lift I.mulLeftEnd : Unitization ℂ A →+* Module.End ℂ I)

theorem unitizationModule_smul_def (u : Unitization ℂ A) (x : I) :
    letI := I.unitizationModule
    u • x = Unitization.lift I.mulLeftEnd u x :=
  (rfl)

@[simp]
theorem coe_unitizationModule_smul (u : Unitization ℂ A) (x : I) :
    letI := I.unitizationModule
    ((u • x : I) : A) = u.fst • (x : A) + u.snd * x := by
  let _ : Module (Unitization ℂ A) I := I.unitizationModule
  simp [unitizationModule_smul_def, Module.algebraMap_end_apply]

/-- Coercing `(r, a) • x` from `I` into `Unitization ℂ A` agrees with multiplication in
`Unitization ℂ A`. -/
theorem inr_coe_unitizationModule_smul (u : Unitization ℂ A) (x : I) :
    letI := I.unitizationModule
    (((u • x : I) : A) : Unitization ℂ A) = u * ((x : A) : Unitization ℂ A) := by
  let _ : Module (Unitization ℂ A) I := I.unitizationModule
  ext
  · simp
  · simp

/-- The left `Unitization ℂ A`-module structure on a closed two-sided ideal `I` is compatible with
its `ℂ`-module structure. -/
theorem isScalarTower_unitizationModule :
    letI := I.unitizationModule
    IsScalarTower ℂ (Unitization ℂ A) I := by
  let _ := I.unitizationModule
  exact ⟨fun r u x => Subtype.ext <| by simp [smul_add, mul_smul, smul_mul_assoc]⟩

theorem mem_annihilator_unitization_iff {u : Unitization ℂ A} :
    (letI := I.unitizationModule; u ∈ Module.annihilator (Unitization ℂ A) I) ↔
      ∀ x ∈ I, u.fst • x + u.snd * x = 0 := by
  let _ := I.unitizationModule
  rw [Module.mem_annihilator]
  refine ⟨fun h x hx => congrArg Subtype.val (h ⟨x, hx⟩), fun h x => Subtype.ext (h x x.property)⟩

/-- The annihilator of a closed two-sided ideal `I` is the preimage in `A` of the module
annihilator of `I` under the left action of the unitization. -/
theorem annihilator_eq_comap_toTwoSided_annihilator :
    letI := I.unitizationModule
    I.annihilator = (Module.annihilator (Unitization ℂ A) I).toTwoSided.comap
      (Unitization.inrNonUnitalAlgHom ℂ A) := by
  let _ : Module (Unitization ℂ A) I := I.unitizationModule
  ext a
  simp [mem_comap, Module.mem_annihilator, ← Subtype.coe_inj]

/-- For a closed two-sided ideal `I` of a nonunital C⋆-algebra `A`, the preimage of
`(Module.annihilator (Unitization ℂ A) I).toTwoSided` along `Unitization.inrNonUnitalAlgHom ℂ A` is
closed. -/
theorem isClosed_comap_toTwoSided_annihilator :
    letI := I.unitizationModule
    IsClosed
      ((TwoSidedIdeal.comap (Unitization.inrNonUnitalAlgHom ℂ A)
          (Module.annihilator (Unitization ℂ A) I).toTwoSided : TwoSidedIdeal A) : Set A) := by
  let _ := I.unitizationModule
  rw [← I.annihilator_eq_comap_toTwoSided_annihilator]
  exact I.isClosed_annihilator

/-- For a closed two-sided ideal `I` of a nonunital C⋆-algebra `A`, the preimage of
`(Module.annihilator (Unitization ℂ A) I).toTwoSided` along `Unitization.inrNonUnitalAlgHom ℂ A` is
closed under complex scalar multiplication. -/
theorem smul_mem_comap_toTwoSided_annihilator (c : ℂ) {a : A} :
    letI := I.unitizationModule
    a ∈ TwoSidedIdeal.comap (Unitization.inrNonUnitalAlgHom ℂ A)
          (Module.annihilator (Unitization ℂ A) I).toTwoSided →
      c • a ∈ TwoSidedIdeal.comap (Unitization.inrNonUnitalAlgHom ℂ A)
          (Module.annihilator (Unitization ℂ A) I).toTwoSided := by
  let _ := I.unitizationModule
  rw [← I.annihilator_eq_comap_toTwoSided_annihilator]
  exact I.smul_mem_annihilator c

/-- For a closed two-sided ideal `I` of a nonunital C⋆-algebra `A`, the preimage of
`(Module.annihilator (Unitization ℂ A) I).toTwoSided` along `Unitization.inrNonUnitalAlgHom ℂ A` is
closed under `star`. -/
theorem star_mem_comap_toTwoSided_annihilator {a : A} :
    letI := I.unitizationModule
    a ∈ TwoSidedIdeal.comap (Unitization.inrNonUnitalAlgHom ℂ A)
          (Module.annihilator (Unitization ℂ A) I).toTwoSided →
      star a ∈ TwoSidedIdeal.comap (Unitization.inrNonUnitalAlgHom ℂ A)
          (Module.annihilator (Unitization ℂ A) I).toTwoSided := by
  let _ := I.unitizationModule
  rw [← I.annihilator_eq_comap_toTwoSided_annihilator]
  exact star_mem_annihilator_of_cstar

end Unitization

section MultiplierHom

section

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- The annihilator of a closed two-sided ideal `I` is the kernel of the canonical homomorphism
from `A` into the multiplier algebra of `I`. -/
theorem ker_multiplierHom (I : TwoSidedIdeal A) [IsClosed (I : Set A)] :
    ker (I.toNonUnitalStarSubalgebra.multiplierHom I.mul_mem_toNonUnitalStarSubalgebra) =
      I.annihilator :=
  ext fun _ ↦ by
    simp only [mem_ker, NonUnitalStarSubalgebra.multiplierHom_eq_zero_iff,
      mem_toNonUnitalStarSubalgebra, mem_annihilator]

/-- The canonical homomorphism from `A` into the multiplier algebra of a closed two-sided ideal `I`
is injective exactly when `I` is essential. -/
theorem multiplierHom_injective_iff_isEssential (I : TwoSidedIdeal A) [IsClosed (I : Set A)] :
    Function.Injective (I.toNonUnitalStarSubalgebra.multiplierHom
      I.mul_mem_toNonUnitalStarSubalgebra) ↔ I.IsEssential := by
  rw [← ker_eq_bot, ker_multiplierHom, annihilator_eq_bot_iff_isEssential_of_isClosed]

/-- The canonical contractive `⋆`-homomorphism `A →⋆ₙₐ[ℂ] 𝓜(ℂ, I)` induced by left and right
multiplication of `A` on a closed two-sided ideal `I`. -/
noncomputable def multiplierHom (I : TwoSidedIdeal A) [IsClosed (I : Set A)] :
    A →⋆ₙₐ[ℂ] 𝓜(ℂ, I) :=
  (DoubleCentralizer.congr I.toNonUnitalStarSubalgebraEquiv.symm).toNonUnitalStarAlgHom.comp
    (I.toNonUnitalStarSubalgebra.multiplierHom I.mul_mem_toNonUnitalStarSubalgebra)

section

variable {I : TwoSidedIdeal A} [IsClosed (I : Set A)]

@[simp]
theorem multiplierHom_fst_apply (a : A) (x : I) :
    (I.multiplierHom a).fst x = ⟨a * x, I.mul_mem_left a x x.property⟩ := by
  ext
  simp [multiplierHom]

@[simp]
theorem multiplierHom_snd_apply (a : A) (x : I) :
    (I.multiplierHom a).snd x = ⟨x * a, I.mul_mem_right x a x.property⟩ := by
  ext
  simp [multiplierHom]

theorem coe_multiplierHom_fst_apply (a : A) (x : I) :
    (((I.multiplierHom a).fst x : I) : A) = a * x := by
  simp

theorem coe_multiplierHom_snd_apply (a : A) (x : I) :
    (((I.multiplierHom a).snd x : I) : A) = x * a := by
  simp

@[simp]
theorem multiplierHom_coe (x : I) : I.multiplierHom (x : A) = (x : 𝓜(ℂ, I)) :=
  DoubleCentralizer.ext_fst_snd (fun _ => Subtype.ext (by simp)) (fun _ => Subtype.ext (by simp))

@[simp]
theorem multiplierHom_comp_starAlgHom :
    I.multiplierHom.comp I.starAlgHom = DoubleCentralizer.coeHom :=
  NonUnitalStarAlgHom.ext fun x => by simp

theorem norm_multiplierHom_le (a : A) : ‖I.multiplierHom a‖ ≤ ‖a‖ :=
  NonUnitalStarAlgHom.norm_apply_le I.multiplierHom a

theorem multiplierHom_eq_zero_iff {a : A} :
    I.multiplierHom a = 0 ↔ a ∈ I.annihilator := by
  let e := DoubleCentralizer.congr I.toNonUnitalStarSubalgebraEquiv.symm
  rw [multiplierHom, NonUnitalStarAlgHom.comp_apply, StarAlgEquiv.toNonUnitalStarAlgHom_apply,
    map_eq_zero_iff e (EmbeddingLike.injective e),
    NonUnitalStarSubalgebra.multiplierHom_eq_zero_iff, mem_annihilator]
  simp only [mem_toNonUnitalStarSubalgebra]

end

/-- The kernel of `I.multiplierHom : A →⋆ₙₐ[ℂ] 𝓜(ℂ, I)` is the annihilator of `I`. -/
@[simp]
theorem ker_idealMultiplierHom (I : TwoSidedIdeal A) [IsClosed (I : Set A)] :
    TwoSidedIdeal.ker I.multiplierHom = I.annihilator := by
  ext a
  rw [mem_ker, multiplierHom_eq_zero_iff]

section

variable {I : TwoSidedIdeal A} [IsClosed (I : Set A)]

theorem multiplierHom_injective_iff_annihilator_eq_bot :
    Function.Injective I.multiplierHom ↔ I.annihilator = ⊥ := by
  rw [← ker_eq_bot, ker_idealMultiplierHom]

/-- For a closed two-sided ideal `I` of a C⋆-algebra `A`, the canonical map `A →⋆ₙₐ[ℂ] 𝓜(ℂ, I)` is
injective if and only if `I` is an essential closed ideal of `A`. -/
theorem multiplierHom_injective_iff_isClosedEssential :
    Function.Injective I.multiplierHom ↔ I.IsClosedEssential := by
  rw [multiplierHom_injective_iff_annihilator_eq_bot,
    isClosedEssential_iff_annihilator_eq_bot]

/-- When `I` is an essential closed ideal of a C⋆-algebra `A`, `I.multiplierHom : A →⋆ₙₐ[ℂ] 𝓜(ℂ, I)`
is an isometric embedding. -/
theorem IsClosedEssential.isometry_multiplierHom (hI : I.IsClosedEssential) :
    Isometry I.multiplierHom :=
  NonUnitalStarAlgHom.isometry I.multiplierHom
    (multiplierHom_injective_iff_isClosedEssential.mpr hI)

end

end

/-- In a unital C⋆-algebra, `I.multiplierHom` sends `1` to `1`. -/
@[simp]
theorem multiplierHom_one {A : Type*} [CStarAlgebra A] (I : TwoSidedIdeal A)
    [IsClosed (I : Set A)] : I.multiplierHom 1 = 1 :=
  DoubleCentralizer.ext_fst_snd (fun _ => Subtype.ext (by simp)) (fun _ => Subtype.ext (by simp))

end MultiplierHom

end TwoSidedIdeal
