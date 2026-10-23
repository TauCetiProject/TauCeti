/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Cochain
public import Mathlib.Algebra.Lie.Solvable
public import Mathlib.Algebra.Lie.TensorProduct
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Low-degree Lie algebra cochains

Complements to Mathlib's low-degree cochain complex `LieModule.Cohomology` of a Lie algebra `L`
with values in an `L`-module `M`.

* `LieModule.Cohomology.range_d₁₂_le_twoCocycle`: every coboundary is a 2-cocycle.
* `LieModule.Cohomology.d₁₂_comp_lieHom_apply_apply_ofTrivial`: with trivial coefficients, `d₁₂`
  commutes with pulling back along a Lie algebra morphism and pushing forward along a linear map.
* `LieModule.Cohomology.twoCochainMap`: pulling 2-cochains back along a Lie algebra morphism and
  pushing them forward along a linear map; with trivial coefficients it preserves 2-cocycles
  (`LieModule.Cohomology.twoCochainMap_mem_twoCocycle`).
* An additive group structure on every submodule of 2-cochains, such as the 2-cocycles, so that
  quotients of such submodules can be formed.
* `LieModule.Cohomology.sub_apply_apply`: the values of a difference of 2-cochains.
* `LieModule.Cohomology.exists_d₁₂_eq_of_forall_dual`: on a perfect Lie algebra, a 2-cochain with
  trivial projective coefficients is a coboundary once its image under every linear functional is
  one.
-/

public section

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]

namespace LieModule.Cohomology

/-- Submodules of 2-cochains are additive groups. Instance search does not find
`Submodule.addCommGroup` here on its own: it cannot recover the ambient module `twoCochain R L M`
by unification, so it is named explicitly. -/
instance instAddCommGroupSubmoduleTwoCochain (S : Submodule R (twoCochain R L M)) :
    AddCommGroup S :=
  Submodule.addCommGroup (M := twoCochain R L M) S

@[simp]
lemma sub_apply_apply (a b : twoCochain R L M) (x y : L) : (a - b) x y = a x y - b x y :=
  (rfl)

variable {L' M' : Type*} [LieRing L'] [LieAlgebra R L'] [AddCommGroup M'] [Module R M']

/-- Pull a 2-cochain back along a Lie algebra morphism `φ` and push it forward along a linear map
`e` of coefficients: `(x, y) ↦ e (c (φ x) (φ y))`. -/
def twoCochainMap (e : M →ₗ[R] M') (φ : L' →ₗ⁅R⁆ L) :
    twoCochain R L M →ₗ[R] twoCochain R L' M' where
  toFun c := ⟨(c.1.compl₁₂ φ.toLinearMap φ.toLinearMap).compr₂ e, fun x ↦ by simp⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp]
lemma twoCochainMap_apply_apply (e : M →ₗ[R] M') (φ : L' →ₗ⁅R⁆ L) (c : twoCochain R L M)
    (x y : L') : twoCochainMap e φ c x y = e (c (φ x) (φ y)) :=
  (rfl)

variable [LieRingModule L M] [LieModule R L M]

/-- Every coboundary is a 2-cocycle. -/
lemma range_d₁₂_le_twoCocycle : LinearMap.range (d₁₂ R L M) ≤ twoCocycle R L M := by
  rintro _ ⟨f, rfl⟩
  rw [mem_twoCocycle_iff, ← LinearMap.comp_apply, d₂₃_comp_d₁₂, LinearMap.zero_apply]

/-- With trivial coefficients, the differential `d₁₂` commutes with pulling one-cochains back along
a Lie algebra morphism `φ` and pushing them forward along a linear map `e` of coefficients. -/
lemma d₁₂_comp_lieHom_apply_apply_ofTrivial [LieRingModule L' M'] [LieModule R L' M']
    [LieModule.IsTrivial L M] [LieModule.IsTrivial L' M'] (e : M →ₗ[R] M') (φ : L' →ₗ⁅R⁆ L)
    (f : oneCochain R L M) (x y : L') :
    d₁₂ R L' M' (e ∘ₗ f ∘ₗ φ.toLinearMap) x y = e (d₁₂ R L M f (φ x) (φ y)) := by
  simp only [d₁₂_apply_apply_ofTrivial, LinearMap.comp_apply, LieHom.coe_toLinearMap,
    LieHom.map_lie, map_neg]

/-- With trivial coefficients, pulling back along a Lie algebra morphism and pushing forward along
a linear map sends 2-cocycles to 2-cocycles. -/
lemma twoCochainMap_mem_twoCocycle [LieRingModule L' M'] [LieModule R L' M']
    [LieModule.IsTrivial L M] [LieModule.IsTrivial L' M'] (e : M →ₗ[R] M') (φ : L' →ₗ⁅R⁆ L)
    {c : twoCochain R L M} (hc : c ∈ twoCocycle R L M) :
    twoCochainMap e φ c ∈ twoCocycle R L' M' := by
  rw [mem_twoCocycle_iff_of_trivial] at hc ⊢
  intro x y z
  simp only [twoCochainMap_apply_apply, LieHom.map_lie, hc (φ x) (φ y) (φ z), map_add]

/-- **On a perfect Lie algebra, coboundaries are detected by functionals.** Let `L` be a perfect Lie
algebra and `M` a projective module with trivial action, for instance a vector space. A 2-cochain
`c` with values in `M` is a coboundary as soon as, for every linear functional `φ` on `M`, the
scalar cochain `φ ∘ c` is the coboundary `(x, y) ↦ -g ⁅x, y⁆` of some linear form `g` on `L`. The
coefficients may be infinitely generated: since `L` is perfect, `c` descends along the bracket
`L ⊗ L → L`, because functionals separate the points of `M`. -/
theorem exists_d₁₂_eq_of_forall_dual [LieModule.IsTrivial L M] [Module.Projective R M]
    (hL : LieAlgebra.derivedSeries R L 1 = ⊤) (c : twoCochain R L M)
    (hc : ∀ φ : Module.Dual R M, ∃ g : Module.Dual R L, ∀ x y : L, φ (c x y) = -g ⁅x, y⁆) :
    ∃ f : oneCochain R L M, d₁₂ R L M f = c := by
  let B := (LieModule.toModuleHom R L L).toLinearMap
  have hB_apply (x y : L) : B (x ⊗ₜ y) = ⁅x, y⁆ := LieModule.toModuleHom_apply R L L x y
  have hB : Function.Surjective B := by
    intro u
    have hu : u ∈ Submodule.span R {⁅x, y⁆ | (x : L) (y : L)} := by
      rw [← LieAlgebra.coe_derivedSeries_one_eq, hL]
      exact Submodule.mem_top
    refine LinearMap.mem_range.mp ((Submodule.span_le.mpr ?_) hu)
    rintro _ ⟨x, y, rfl⟩
    exact ⟨x ⊗ₜ y, hB_apply x y⟩
  -- The kernel of the bracket is killed by every functional applied to `c`, hence by `c`.
  have hker : LinearMap.ker B ≤ LinearMap.ker (TensorProduct.lift c.1) := by
    intro w hw
    refine LinearMap.mem_ker.mpr ((Module.forall_dual_apply_eq_zero_iff R _).mp fun φ ↦ ?_)
    obtain ⟨g, hg⟩ := hc φ
    have hφ : φ ∘ₗ TensorProduct.lift c.1 = -(g ∘ₗ B) :=
      TensorProduct.ext' fun x y ↦ by simp [hB_apply, hg]
    simpa [LinearMap.mem_ker.mp hw] using LinearMap.congr_fun hφ w
  refine ⟨-B.liftOfSurjective hB ⟨_, hker⟩, Subtype.ext (LinearMap.ext₂ fun x y ↦ ?_)⟩
  rw [twoCochain_val_apply, d₁₂_apply_apply_ofTrivial, ← hB_apply, LinearMap.neg_apply, neg_neg,
    LinearMap.equivOfSurjective_apply, TensorProduct.lift.tmul, twoCochain_val_apply]

end LieModule.Cohomology
