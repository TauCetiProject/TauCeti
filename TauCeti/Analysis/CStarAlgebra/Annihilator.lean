/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Hom
public import TauCeti.Analysis.CStarAlgebra.Ideal
public import TauCeti.Analysis.CStarAlgebra.Multiplier

/-!
# Annihilators and essential ideals in C⋆-algebras

In a possibly nonunital C⋆-algebra `A`, every closed two-sided ideal is closed under `star`
(`TwoSidedIdeal.star_mem_of_isClosed`), and taking topological closure does not change the left or
right annihilator (`TwoSidedIdeal.leftAnnihilator_topologicalClosure`). Combining these with the
properness of the involution yields the full C⋆-algebra annihilator theory for *all* two-sided
ideals `I : TwoSidedIdeal A` (closed or not):
* `I.leftAnnihilator` is a closed two-sided ideal of `A`, hence a C⋆-subalgebra absorbing complex
  scalars and `star`;
* left and right annihilation coincide (`I.leftAnnihilator = I.rightAnnihilator`);
* `I` meets its annihilator trivially (`I ⊓ I.leftAnnihilator = ⊥`), `I.topologicalClosure ≤
  I.leftAnnihilator.leftAnnihilator`, and `I.leftAnnihilator.leftAnnihilator.leftAnnihilator =
  I.leftAnnihilator`;
* essentiality among closed ideals, algebraic essentiality, and triviality of the annihilator are
  all equivalent (`I.IsClosedEssential ↔ I.IsEssential ↔ I.leftAnnihilator = ⊥`).

In the unital case `[CStarAlgebra A]`, `I.leftAnnihilator` agrees with
`(Module.annihilator A I).toTwoSided`, and closedness, complex scalar absorption, and
`star`-invariance transfer directly to `Module.annihilator A I` and its two-sided bundling.

In the nonunital case `[NonUnitalCStarAlgebra A]`, a closed two-sided ideal `I` absorbs complex
scalars (`TwoSidedIdeal.smul_mem_of_isClosed`), hence carries the left `Unitization ℂ A`-module
action `(r, a) • x = r • x + a * x` (`TwoSidedIdeal.unitizationSMul`,
`TwoSidedIdeal.unitizationModule`, provided as definitions taking `IsClosed (I : Set A)` rather than
global instances). Under this action, `I.leftAnnihilator` coincides with
`TwoSidedIdeal.comap (Unitization.inrNonUnitalAlgHom ℂ A)` applied to
`(Module.annihilator (Unitization ℂ A) I).toTwoSided`
(`TwoSidedIdeal.leftAnnihilator_eq_comap_unitization`), and closedness, complex-linearity, and
`star`-invariance transport across this identification.

Finally, for any closed two-sided ideal `I`, the canonical contractive `⋆`-homomorphism
`I.multiplierHom : A →⋆ₙₐ[ℂ] 𝓜(ℂ, I)` into the multiplier algebra of `I` has kernel
`I.leftAnnihilator`, so `I.multiplierHom` is injective precisely when `I.IsClosedEssential`.

## Main definitions and results

* `TwoSidedIdeal.leftAnnihilator_eq_rightAnnihilator`, `TwoSidedIdeal.inf_leftAnnihilator_eq_bot`,
  `TwoSidedIdeal.topologicalClosure_le_leftAnnihilator_leftAnnihilator`, and
  `TwoSidedIdeal.isClosedEssential_iff_leftAnnihilator_eq_bot`: symmetry, disjointness, double
  annihilator inclusion, and essentiality in any `NonUnitalCStarAlgebra`.
* `TwoSidedIdeal.isClosed_annihilator_toTwoSided`, `TwoSidedIdeal.smul_mem_annihilator_toTwoSided`,
  and `TwoSidedIdeal.star_mem_annihilator_toTwoSided`: property transport for
  `(Module.annihilator A I).toTwoSided` in unital C⋆-algebras.
* `TwoSidedIdeal.unitizationSMul`, `TwoSidedIdeal.unitizationModule`, and
  `TwoSidedIdeal.leftAnnihilator_eq_comap_unitization`: left `Unitization ℂ A`-module action on a
  closed ideal `I` and identification of `I.leftAnnihilator` with the pullback of
  `Module.annihilator (Unitization ℂ A) I`, together with property-transport lemmas.
* `TwoSidedIdeal.multiplierHom`, `TwoSidedIdeal.ker_multiplierHom`, and
  `TwoSidedIdeal.multiplierHom_injective_iff_isClosedEssential`: the canonical homomorphism
  `A →⋆ₙₐ[ℂ] 𝓜(ℂ, I)` and its kernel and injectivity characterizations.

## References

* Bruce Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*, §II.5.4.7.
* Gerard J. Murphy, *C*-Algebras and Operator Theory*, §3.1.
* Iain Raeburn and Dana Williams, *Morita Equivalence and Continuous-Trace C*-Algebras*,
  Proposition 2.54.
-/

public section

open scoped CStarAlgebra MultiplierAlgebra

namespace TwoSidedIdeal

section NonUnitalCStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- In any C⋆-algebra, the left and right annihilators of a two-sided ideal `I` coincide: passing to
`I.topologicalClosure` preserves both annihilators and yields a `star`-closed ideal. -/
theorem leftAnnihilator_eq_rightAnnihilator (I : TwoSidedIdeal A) :
    I.leftAnnihilator = I.rightAnnihilator := by
  have _ : IsClosed (I.topologicalClosure : Set A) := I.isClosed_topologicalClosure
  rw [← I.leftAnnihilator_topologicalClosure, ← I.rightAnnihilator_topologicalClosure]
  exact leftAnnihilator_eq_rightAnnihilator_of_star_mem I.topologicalClosure.star_mem_of_isClosed

theorem mem_leftAnnihilator_iff_mul_right {I : TwoSidedIdeal A} {a : A} :
    a ∈ I.leftAnnihilator ↔ ∀ x ∈ I, x * a = 0 := by
  rw [I.leftAnnihilator_eq_rightAnnihilator, mem_rightAnnihilator]

/-- The left annihilator of any two-sided ideal in a C⋆-algebra is closed under `star`. -/
theorem star_mem_leftAnnihilator {I : TwoSidedIdeal A} {a : A} (ha : a ∈ I.leftAnnihilator) :
    star a ∈ I.leftAnnihilator :=
  I.leftAnnihilator.star_mem_of_isClosed ha

/-- The right annihilator of any two-sided ideal in a C⋆-algebra is closed under `star`. -/
theorem star_mem_rightAnnihilator {I : TwoSidedIdeal A} {a : A} (ha : a ∈ I.rightAnnihilator) :
    star a ∈ I.rightAnnihilator :=
  I.rightAnnihilator.star_mem_of_isClosed ha

/-- Every two-sided ideal of a C⋆-algebra has trivial intersection with its annihilator. -/
@[simp]
theorem inf_leftAnnihilator_eq_bot (I : TwoSidedIdeal A) : I ⊓ I.leftAnnihilator = ⊥ := by
  have _ : IsClosed (I.topologicalClosure : Set A) := I.isClosed_topologicalClosure
  refine le_bot_iff.mp ((inf_le_inf_right I.leftAnnihilator I.le_topologicalClosure).trans ?_)
  rw [← I.leftAnnihilator_topologicalClosure,
    inf_leftAnnihilator_eq_bot_of_star_mem I.topologicalClosure.star_mem_of_isClosed]

@[simp]
theorem leftAnnihilator_inf_eq_bot (I : TwoSidedIdeal A) : I.leftAnnihilator ⊓ I = ⊥ := by
  rw [inf_comm, I.inf_leftAnnihilator_eq_bot]

theorem coe_inter_leftAnnihilator (I : TwoSidedIdeal A) :
    (I : Set A) ∩ (I.leftAnnihilator : Set A) = {0} := by
  calc (I : Set A) ∩ (I.leftAnnihilator : Set A)
      = ((I ⊓ I.leftAnnihilator : TwoSidedIdeal A) : Set A) := rfl
    _ = ((⊥ : TwoSidedIdeal A) : Set A) := by rw [I.inf_leftAnnihilator_eq_bot]
    _ = {0} := coe_bot A

/-- The topological closure of `I` is contained in its double annihilator. -/
theorem topologicalClosure_le_leftAnnihilator_leftAnnihilator (I : TwoSidedIdeal A) :
    I.topologicalClosure ≤ I.leftAnnihilator.leftAnnihilator := by
  have _ : IsClosed (I.topologicalClosure : Set A) := I.isClosed_topologicalClosure
  simpa only [I.leftAnnihilator_topologicalClosure] using
    le_leftAnnihilator_leftAnnihilator_of_star_mem I.topologicalClosure.star_mem_of_isClosed

theorem le_leftAnnihilator_leftAnnihilator (I : TwoSidedIdeal A) :
    I ≤ I.leftAnnihilator.leftAnnihilator :=
  I.le_topologicalClosure.trans I.topologicalClosure_le_leftAnnihilator_leftAnnihilator

@[simp]
theorem leftAnnihilator_leftAnnihilator_leftAnnihilator (I : TwoSidedIdeal A) :
    I.leftAnnihilator.leftAnnihilator.leftAnnihilator = I.leftAnnihilator :=
  le_antisymm
    (leftAnnihilator_anti I.le_leftAnnihilator_leftAnnihilator)
    I.leftAnnihilator.le_leftAnnihilator_leftAnnihilator

/-- In a C⋆-algebra, a two-sided ideal `J` annihilates `I` if and only if `I ⊓ J = ⊥`. -/
theorem le_leftAnnihilator_iff_inf_eq_bot {I J : TwoSidedIdeal A} :
    J ≤ I.leftAnnihilator ↔ I ⊓ J = ⊥ :=
  ⟨fun h => le_bot_iff.mp ((inf_le_inf_left I h).trans I.inf_leftAnnihilator_eq_bot.le),
   le_leftAnnihilator_of_inf_eq_bot⟩

/-- A two-sided ideal of a C⋆-algebra is essential among closed ideals if and only if its left
annihilator is `⊥`. -/
theorem isClosedEssential_iff_leftAnnihilator_eq_bot {I : TwoSidedIdeal A} :
    I.IsClosedEssential ↔ I.leftAnnihilator = ⊥ :=
  ⟨fun h => isClosedEssential_iff_eq_bot.mp h I.leftAnnihilator I.isClosed_leftAnnihilator
      I.inf_leftAnnihilator_eq_bot,
   isClosedEssential_of_leftAnnihilator_eq_bot⟩

theorem isClosedEssential_iff_rightAnnihilator_eq_bot {I : TwoSidedIdeal A} :
    I.IsClosedEssential ↔ I.rightAnnihilator = ⊥ := by
  rw [isClosedEssential_iff_leftAnnihilator_eq_bot, I.leftAnnihilator_eq_rightAnnihilator]

/-- In a C⋆-algebra, essentiality among closed two-sided ideals and algebraic essentiality among all
two-sided ideals are equivalent. -/
theorem isClosedEssential_iff_isEssential {I : TwoSidedIdeal A} :
    I.IsClosedEssential ↔ I.IsEssential :=
  ⟨fun h => isEssential_of_leftAnnihilator_eq_bot
      (isClosedEssential_iff_leftAnnihilator_eq_bot.mp h),
   IsEssential.isClosedEssential⟩

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
  rw [isClosedEssential_iff_leftAnnihilator_eq_bot, isClosedEssential_iff_leftAnnihilator_eq_bot,
    I.leftAnnihilator_topologicalClosure]

end NonUnitalCStarAlgebra

section UnitalCStarAlgebra

variable {A : Type*} [CStarAlgebra A]

/-- Membership in `(Module.annihilator A I).toTwoSided` for a two-sided ideal `I` of a unital
C⋆-algebra. -/
theorem mem_annihilator_toTwoSided_iff {I : TwoSidedIdeal A} {a : A} :
    a ∈ (Module.annihilator A I).toTwoSided ↔ ∀ x ∈ I, a * x = 0 := by
  rw [← leftAnnihilator_eq_annihilator, mem_leftAnnihilator]

/-- Transport of closedness from `I.leftAnnihilator` to `(Module.annihilator A I).toTwoSided`. -/
instance isClosed_annihilator_toTwoSided (I : TwoSidedIdeal A) :
    IsClosed (((Module.annihilator A I).toTwoSided : TwoSidedIdeal A) : Set A) :=
  I.leftAnnihilator_eq_annihilator ▸ I.isClosed_leftAnnihilator

/-- Transport of closedness from `I.leftAnnihilator` to `Module.annihilator A I`. -/
instance isClosed_annihilator (I : TwoSidedIdeal A) :
    IsClosed (Module.annihilator A I : Set A) := by
  simpa only [Ideal.coe_toTwoSided] using isClosed_annihilator_toTwoSided I

/-- Transport of complex scalar absorption to `(Module.annihilator A I).toTwoSided`. -/
theorem smul_mem_annihilator_toTwoSided (I : TwoSidedIdeal A) (c : ℂ) {a : A}
    (ha : a ∈ (Module.annihilator A I).toTwoSided) :
    c • a ∈ (Module.annihilator A I).toTwoSided := by
  rw [← leftAnnihilator_eq_annihilator] at ha ⊢
  exact I.smul_mem_leftAnnihilator c ha

/-- Transport of `star`-invariance to `(Module.annihilator A I).toTwoSided`. -/
theorem star_mem_annihilator_toTwoSided {I : TwoSidedIdeal A} {a : A}
    (ha : a ∈ (Module.annihilator A I).toTwoSided) :
    star a ∈ (Module.annihilator A I).toTwoSided := by
  rw [← leftAnnihilator_eq_annihilator] at ha ⊢
  exact star_mem_leftAnnihilator ha

/-- Transport of `star`-invariance to `Module.annihilator A I`. -/
theorem star_mem_annihilator {I : TwoSidedIdeal A} {a : A} (ha : a ∈ Module.annihilator A I) :
    star a ∈ Module.annihilator A I :=
  Ideal.mem_toTwoSided.mp (star_mem_annihilator_toTwoSided (Ideal.mem_toTwoSided.mpr ha))

end UnitalCStarAlgebra

section Unitization

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- Left scalar action `(r, a) • x = r • x + a * x` of `Unitization ℂ A` on a closed two-sided
ideal `I : TwoSidedIdeal A`. Provided as a definition taking the closedness hypothesis rather than
as a global instance. -/
@[instance_reducible]
def unitizationSMul (I : TwoSidedIdeal A) (hI : IsClosed (I : Set A)) :
    SMul (Unitization ℂ A) I :=
  I.unitizationSMulOfSMulMem fun r _ hx => @smul_mem_of_isClosed A _ I hI r _ hx

theorem coe_unitizationSMul (I : TwoSidedIdeal A) (hI : IsClosed (I : Set A))
    (u : Unitization ℂ A) (x : I) :
    (letI := I.unitizationSMul hI; ((u • x : I) : A)) = u.fst • (x : A) + u.snd * (x : A) :=
  I.coe_unitizationSMulOfSMulMem _ u x

theorem inr_coe_unitizationSMul (I : TwoSidedIdeal A) (hI : IsClosed (I : Set A))
    (u : Unitization ℂ A) (x : I) :
    (letI := I.unitizationSMul hI; (((u • x : I) : A) : Unitization ℂ A)) =
      u * ((x : A) : Unitization ℂ A) :=
  I.inr_coe_unitizationSMulOfSMulMem _ u x

/-- Left `Unitization ℂ A`-module structure `(r, a) • x = r • x + a * x` on a closed two-sided
ideal `I : TwoSidedIdeal A`. Provided as a definition taking `IsClosed (I : Set A)` rather than as a
global instance. -/
@[instance_reducible]
def unitizationModule (I : TwoSidedIdeal A) (hI : IsClosed (I : Set A)) :
    Module (Unitization ℂ A) I :=
  I.unitizationModuleOfSMulMem fun r _ hx => @smul_mem_of_isClosed A _ I hI r _ hx

theorem mem_annihilator_unitization_iff (I : TwoSidedIdeal A) (hI : IsClosed (I : Set A))
    {u : Unitization ℂ A} :
    (letI := I.unitizationModule hI; u ∈ Module.annihilator (Unitization ℂ A) I) ↔
      ∀ x ∈ I, u.fst • x + u.snd * x = 0 :=
  I.mem_annihilator_unitizationOfSMulMem_iff _

/-- For a closed two-sided ideal `I` of a nonunital C⋆-algebra `A`, `I.leftAnnihilator` coincides
with the preimage of `(Module.annihilator (Unitization ℂ A) I).toTwoSided` along
`Unitization.inrNonUnitalAlgHom ℂ A`. -/
theorem leftAnnihilator_eq_comap_unitization (I : TwoSidedIdeal A) (hI : IsClosed (I : Set A)) :
    letI := I.unitizationModule hI
    I.leftAnnihilator =
      TwoSidedIdeal.comap (Unitization.inrNonUnitalAlgHom ℂ A)
        (Module.annihilator (Unitization ℂ A) I).toTwoSided :=
  I.leftAnnihilator_eq_comap_unitization_of_smul_mem _

/-- Transport of closedness across `leftAnnihilator_eq_comap_unitization`. -/
theorem isClosed_comap_annihilator_unitization (I : TwoSidedIdeal A) (hI : IsClosed (I : Set A)) :
    letI := I.unitizationModule hI
    IsClosed
      ((TwoSidedIdeal.comap (Unitization.inrNonUnitalAlgHom ℂ A)
          (Module.annihilator (Unitization ℂ A) I).toTwoSided : TwoSidedIdeal A) : Set A) := by
  let _ := I.unitizationModule hI
  rw [← I.leftAnnihilator_eq_comap_unitization hI]
  exact I.isClosed_leftAnnihilator

/-- Transport of complex scalar absorption across `leftAnnihilator_eq_comap_unitization`. -/
theorem smul_mem_comap_annihilator_unitization (I : TwoSidedIdeal A) (hI : IsClosed (I : Set A))
    (c : ℂ) {a : A} :
    letI := I.unitizationModule hI
    a ∈ TwoSidedIdeal.comap (Unitization.inrNonUnitalAlgHom ℂ A)
          (Module.annihilator (Unitization ℂ A) I).toTwoSided →
      c • a ∈ TwoSidedIdeal.comap (Unitization.inrNonUnitalAlgHom ℂ A)
          (Module.annihilator (Unitization ℂ A) I).toTwoSided := by
  let _ := I.unitizationModule hI
  rw [← I.leftAnnihilator_eq_comap_unitization hI]
  exact I.smul_mem_leftAnnihilator c

/-- Transport of `star`-invariance across `leftAnnihilator_eq_comap_unitization`. -/
theorem star_mem_comap_annihilator_unitization (I : TwoSidedIdeal A) (hI : IsClosed (I : Set A))
    {a : A} :
    letI := I.unitizationModule hI
    a ∈ TwoSidedIdeal.comap (Unitization.inrNonUnitalAlgHom ℂ A)
          (Module.annihilator (Unitization ℂ A) I).toTwoSided →
      star a ∈ TwoSidedIdeal.comap (Unitization.inrNonUnitalAlgHom ℂ A)
          (Module.annihilator (Unitization ℂ A) I).toTwoSided := by
  let _ := I.unitizationModule hI
  rw [← I.leftAnnihilator_eq_comap_unitization hI]
  exact star_mem_leftAnnihilator

end Unitization

section MultiplierHom

variable {A : Type*} [NonUnitalCStarAlgebra A] (I : TwoSidedIdeal A) [IsClosed (I : Set A)]

/-- The canonical contractive `⋆`-homomorphism `A →⋆ₙₐ[ℂ] 𝓜(ℂ, I)` induced by left and right
multiplication of `A` on a closed two-sided ideal `I`, transported from
`NonUnitalStarSubalgebra.multiplierHom` along `I.toNonUnitalStarSubalgebraEquiv`. -/
noncomputable def multiplierHom : A →⋆ₙₐ[ℂ] 𝓜(ℂ, I) :=
  (DoubleCentralizer.congr I.toNonUnitalStarSubalgebraEquiv.symm).toNonUnitalStarAlgHom.comp
    (I.toNonUnitalStarSubalgebra.multiplierHom fun a x hx =>
      I.mem_toNonUnitalStarSubalgebra.mpr
        (I.mul_mem_left a x (I.mem_toNonUnitalStarSubalgebra.mp hx)))

variable {I}

@[simp]
theorem multiplierHom_fst_apply (a : A) (x : I) :
    (I.multiplierHom a).fst x = ⟨a * x, I.mul_mem_left a x x.2⟩ := by
  ext
  simp [multiplierHom]

@[simp]
theorem multiplierHom_snd_apply (a : A) (x : I) :
    (I.multiplierHom a).snd x = ⟨x * a, I.mul_mem_right x a x.2⟩ := by
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

theorem norm_multiplierHom_le (a : A) : ‖I.multiplierHom a‖ ≤ ‖a‖ := by
  let e := DoubleCentralizer.congr I.toNonUnitalStarSubalgebraEquiv.symm
  rw [multiplierHom, NonUnitalStarAlgHom.comp_apply, StarAlgEquiv.toNonUnitalStarAlgHom_apply,
    NonUnitalStarAlgHom.norm_map e (EmbeddingLike.injective e)]
  exact I.toNonUnitalStarSubalgebra.norm_multiplierHom_le _ a

theorem multiplierHom_eq_zero_iff {a : A} :
    I.multiplierHom a = 0 ↔ a ∈ I.leftAnnihilator := by
  let e := DoubleCentralizer.congr I.toNonUnitalStarSubalgebraEquiv.symm
  rw [multiplierHom, NonUnitalStarAlgHom.comp_apply, StarAlgEquiv.toNonUnitalStarAlgHom_apply,
    map_eq_zero_iff e (EmbeddingLike.injective e),
    NonUnitalStarSubalgebra.multiplierHom_eq_zero_iff, mem_leftAnnihilator]
  simp only [mem_toNonUnitalStarSubalgebra]

/-- The kernel of `I.multiplierHom : A →⋆ₙₐ[ℂ] 𝓜(ℂ, I)` is the left annihilator of `I`. -/
@[simp]
theorem ker_multiplierHom (I : TwoSidedIdeal A) [IsClosed (I : Set A)] :
    TwoSidedIdeal.ker I.multiplierHom = I.leftAnnihilator := by
  ext a
  rw [mem_ker, multiplierHom_eq_zero_iff]

theorem multiplierHom_injective_iff_leftAnnihilator_eq_bot :
    Function.Injective I.multiplierHom ↔ I.leftAnnihilator = ⊥ := by
  rw [injective_iff_map_eq_zero, eq_bot_iff]
  refine ⟨fun h a ha => (mem_bot _).mpr (h a (multiplierHom_eq_zero_iff.mpr ha)),
    fun h a ha => (mem_bot _).mp (h (multiplierHom_eq_zero_iff.mp ha))⟩

/-- For a closed two-sided ideal `I` of a C⋆-algebra `A`, the canonical map `A →⋆ₙₐ[ℂ] 𝓜(ℂ, I)` is
injective if and only if `I` is an essential closed ideal of `A`. -/
theorem multiplierHom_injective_iff_isClosedEssential :
    Function.Injective I.multiplierHom ↔ I.IsClosedEssential := by
  rw [multiplierHom_injective_iff_leftAnnihilator_eq_bot,
    isClosedEssential_iff_leftAnnihilator_eq_bot]

/-- When `I` is an essential closed ideal of a C⋆-algebra `A`, `I.multiplierHom : A →⋆ₙₐ[ℂ] 𝓜(ℂ, I)`
is an isometric embedding. -/
theorem IsClosedEssential.isometry_multiplierHom (hI : I.IsClosedEssential) :
    Isometry I.multiplierHom :=
  NonUnitalStarAlgHom.isometry I.multiplierHom
    (multiplierHom_injective_iff_isClosedEssential.mpr hI)

end MultiplierHom

section Prod

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

@[simp]
theorem leftAnnihilator_ker_snd_nonUnitalStarAlgHom :
    (TwoSidedIdeal.ker (NonUnitalStarAlgHom.snd ℂ A B)).leftAnnihilator =
      TwoSidedIdeal.ker (NonUnitalStarAlgHom.fst ℂ A B) := by
  have hsnd : TwoSidedIdeal.ker (NonUnitalStarAlgHom.snd ℂ A B) =
      TwoSidedIdeal.ker (NonUnitalRingHom.snd A B) := rfl
  have hfst : TwoSidedIdeal.ker (NonUnitalStarAlgHom.fst ℂ A B) =
      TwoSidedIdeal.ker (NonUnitalRingHom.fst A B) := rfl
  rw [hsnd, hfst, leftAnnihilator_ker_snd]

@[simp]
theorem leftAnnihilator_ker_fst_nonUnitalStarAlgHom :
    (TwoSidedIdeal.ker (NonUnitalStarAlgHom.fst ℂ A B)).leftAnnihilator =
      TwoSidedIdeal.ker (NonUnitalStarAlgHom.snd ℂ A B) := by
  have hfst : TwoSidedIdeal.ker (NonUnitalStarAlgHom.fst ℂ A B) =
      TwoSidedIdeal.ker (NonUnitalRingHom.fst A B) := rfl
  have hsnd : TwoSidedIdeal.ker (NonUnitalStarAlgHom.snd ℂ A B) =
      TwoSidedIdeal.ker (NonUnitalRingHom.snd A B) := rfl
  rw [hfst, hsnd, leftAnnihilator_ker_fst]

@[simp]
theorem isClosedEssential_ker_snd_nonUnitalStarAlgHom_iff :
    (TwoSidedIdeal.ker (NonUnitalStarAlgHom.snd ℂ A B)).IsClosedEssential ↔ Subsingleton B := by
  rw [isClosedEssential_iff_leftAnnihilator_eq_bot, leftAnnihilator_ker_snd_nonUnitalStarAlgHom,
    eq_bot_iff]
  refine ⟨fun h => ⟨fun b₁ b₂ => ?_⟩, fun _ p hp => ?_⟩
  · have hmem : ((0 : A), b₁ - b₂) ∈ TwoSidedIdeal.ker (NonUnitalStarAlgHom.fst ℂ A B) := by
      simp [mem_ker]
    have hzero : ((0 : A), b₁ - b₂) = 0 := (mem_bot _).mp (h hmem)
    exact sub_eq_zero.mp (congrArg Prod.snd hzero)
  · have hp1 : p.1 = 0 := by simpa [mem_ker] using hp
    refine (mem_bot _).mpr ?_
    ext
    · exact hp1
    · exact Subsingleton.elim p.2 0

@[simp]
theorem isClosedEssential_ker_fst_nonUnitalStarAlgHom_iff :
    (TwoSidedIdeal.ker (NonUnitalStarAlgHom.fst ℂ A B)).IsClosedEssential ↔ Subsingleton A := by
  rw [isClosedEssential_iff_leftAnnihilator_eq_bot, leftAnnihilator_ker_fst_nonUnitalStarAlgHom,
    eq_bot_iff]
  refine ⟨fun h => ⟨fun a₁ a₂ => ?_⟩, fun _ p hp => ?_⟩
  · have hmem : (a₁ - a₂, (0 : B)) ∈ TwoSidedIdeal.ker (NonUnitalStarAlgHom.snd ℂ A B) := by
      simp [mem_ker]
    have hzero : (a₁ - a₂, (0 : B)) = 0 := (mem_bot _).mp (h hmem)
    exact sub_eq_zero.mp (congrArg Prod.fst hzero)
  · have hp2 : p.2 = 0 := by simpa [mem_ker] using hp
    refine (mem_bot _).mpr ?_
    ext
    · exact Subsingleton.elim p.1 0
    · exact hp2

end Prod

end TwoSidedIdeal
