/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.CharacterModule
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.Projective

/-!
# The character module of a left module over a noncommutative ring

The character module `M⁺ = Hom_ℤ(M, ℚ / ℤ)` of a left `A`-module `M` is a right `A`-module, that is,
an `Aᵐᵒᵖ`-module. Mathlib's `CharacterModule` carries an action only of a commutative ring, so this
file supplies the right action and the part of Lambek's duality between flat and injective modules
that makes sense without a tensor product over `A`: the character module of a projective module is
injective, and conversely a finitely presented module with injective character module is projective.
This is what lets one compare projective dimensions of left modules with injective dimensions of
right modules, and so left with right global dimension.

## Main definitions

* `CharacterModule.instModuleMulOpposite`: the scoped `Aᵐᵒᵖ`-module structure on `M⁺`.
* `CharacterModule.opDual`: the `Aᵐᵒᵖ`-linear map on character modules induced by an `A`-linear map.

## Main results

* `CharacterModule.exact_opDual`: taking character modules is exact.
* `CharacterModule.injective_of_projective`: the character module of a projective module is
  injective.
* `CharacterModule.injective_iff_projective`: a finitely presented module is projective exactly when
  its character module is injective.

## References

* J. Lambek, *A module is flat if and only if its character module is injective*, Canad. Math. Bull.
  7 (1964), 237–243.
-/

public section

universe u v w

open MulOpposite

namespace CharacterModule

variable {A : Type u} [Ring A]
variable {M : Type v} [AddCommGroup M] [Module A M] {N : Type w} [AddCommGroup N] [Module A N]

/-- The character module `Hom_ℤ(M, ℚ / ℤ)` of a left `A`-module `M` is a right `A`-module, by
`(χ · a) m = χ (a m)`. This instance is scoped: over a commutative ring it would compete with
Mathlib's action on the character module of an `Aᵐᵒᵖ`-module. -/
scoped instance instModuleMulOpposite : Module Aᵐᵒᵖ (CharacterModule M) :=
  inferInstanceAs (Module Aᵈᵐᵃ (M →+ AddCircle (1 : ℚ)))

/-- The right action on a character module is precomposition with the left action. -/
@[simp]
theorem mulOpposite_smul_apply (a : Aᵐᵒᵖ) (χ : CharacterModule M) (m : M) :
    (a • χ) m = χ (a.unop • m) := (rfl)

/-- The map `N⁺ → M⁺` of right `A`-modules induced by a map `f : M → N` of left `A`-modules, given
by precomposition with `f`. -/
def opDual (f : M →ₗ[A] N) : CharacterModule N →ₗ[Aᵐᵒᵖ] CharacterModule M where
  toFun χ := AddMonoidHom.comp χ f.toAddMonoidHom
  map_add' _ _ := rfl
  map_smul' a χ := DFunLike.ext _ _ fun m ↦ congrArg χ (f.map_smul a.unop m).symm

/-- `opDual f` is precomposition with `f`. -/
@[simp]
theorem opDual_apply (f : M →ₗ[A] N) (χ : CharacterModule N) (m : M) :
    opDual f χ m = χ (f m) := (rfl)

/-- A surjection of left modules induces an injection of character modules. -/
theorem opDual_injective_of_surjective (f : M →ₗ[A] N) (hf : Function.Surjective f) :
    Function.Injective (opDual f) := fun χ χ' h ↦ DFunLike.ext _ _ fun n ↦ by
  obtain ⟨m, rfl⟩ := hf n
  exact DFunLike.congr_fun h m

/-- An injection of left modules induces a surjection of character modules, since `ℚ / ℤ` is
divisible. -/
theorem opDual_surjective_of_injective (f : M →ₗ[A] N) (hf : Function.Injective f) :
    Function.Surjective (opDual f) := fun χ ↦ by
  obtain ⟨χ', hχ'⟩ := (Module.Baer.of_divisible (AddCircle (1 : ℚ))).extension_property_addMonoidHom
    f.toAddMonoidHom hf χ
  exact ⟨χ', hχ'⟩

/-- Taking character modules is exact: an exact sequence `K → M → N` of left modules induces an
exact sequence `N⁺ → M⁺ → K⁺` of right modules. -/
theorem exact_opDual {K : Type*} [AddCommGroup K] [Module A K] {i : K →ₗ[A] M} {f : M →ₗ[A] N}
    (h : Function.Exact i f) : Function.Exact (opDual f) (opDual i) := by
  intro χ
  constructor
  · intro hχ
    have hker : ∀ m, f m = 0 → χ m = 0 := fun m hm ↦ by
      obtain ⟨k, rfl⟩ := (h m).mp hm
      exact DFunLike.congr_fun hχ k
    let g : M →+ f.range := f.rangeRestrict.toAddMonoidHom
    have hg : Function.Surjective g := f.surjective_rangeRestrict
    let χ₀ : f.range →+ AddCircle (1 : ℚ) := g.liftOfSurjective hg
      ⟨χ, fun m hm ↦ hker m (congrArg Subtype.val hm)⟩
    obtain ⟨χ', hχ'⟩ := (Module.Baer.of_divisible _).extension_property_addMonoidHom
      f.range.subtype.toAddMonoidHom Subtype.val_injective χ₀
    refine ⟨χ', DFunLike.ext _ _ fun m ↦ ?_⟩
    have h₁ := DFunLike.congr_fun hχ' (g m)
    have h₂ : χ₀ (g m) = χ m := g.liftOfRightInverse_comp_apply _ _ _ m
    exact h₁.trans h₂
  · rintro ⟨χ', rfl⟩
    exact DFunLike.ext _ _ fun k ↦
      (congrArg χ' (h.apply_apply_eq_zero k)).trans (map_zero χ')

/-- The character module of a projective left module is an injective right module. -/
theorem injective_of_projective {P : Type v} [AddCommGroup P] [Module A P]
    [Module.Projective A P] : Module.Injective Aᵐᵒᵖ (CharacterModule P) where
  out X Y _ _ _ _ i hi g := by
    -- Swap the arguments: `Hom_{Aᵐᵒᵖ}(X, P⁺)` is `Hom_A(P, X⁺)`, for the left `A`-action on `X⁺`,
    -- and `Y⁺ → X⁺` is surjective because `ℚ / ℤ` is divisible.
    let actX : Module A (CharacterModule X) := Module.compHom _ (RingEquiv.opOp A).toRingHom
    let actY : Module A (CharacterModule Y) := Module.compHom _ (RingEquiv.opOp A).toRingHom
    let π : CharacterModule Y →ₗ[A] CharacterModule X :=
      { toFun := fun χ ↦ AddMonoidHom.comp χ i.toAddMonoidHom
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun a χ ↦ DFunLike.ext _ _ fun x ↦
          congrArg χ (i.map_smul (op a) x).symm }
    have hπ : Function.Surjective π := fun χ ↦ by
      obtain ⟨χ', hχ'⟩ := (Module.Baer.of_divisible _).extension_property_addMonoidHom
        i.toAddMonoidHom hi χ
      exact ⟨χ', hχ'⟩
    let swap : P →ₗ[A] CharacterModule X :=
      { toFun := fun p ↦ AddMonoidHom.mk' (fun x ↦ g x p) fun x x' ↦
          DFunLike.congr_fun (map_add g x x') p
        map_add' := fun p p' ↦ DFunLike.ext _ _ fun x ↦ map_add (g x) p p'
        map_smul' := fun a p ↦ DFunLike.ext _ _ fun x ↦
          (DFunLike.congr_fun (g.map_smul (op a) x) p).symm }
    obtain ⟨h, hh⟩ := Module.projective_lifting_property π swap hπ
    exact ⟨{ toFun := fun y ↦ AddMonoidHom.mk' (fun p ↦ h p y) fun p p' ↦
               DFunLike.congr_fun (map_add h p p') y
             map_add' := fun y y' ↦ DFunLike.ext _ _ fun p ↦ map_add (h p) y y'
             map_smul' := fun a y ↦ DFunLike.ext _ _ fun p ↦
               (DFunLike.congr_fun (h.map_smul a.unop p) y).symm },
      fun x ↦ DFunLike.ext _ _ fun p ↦ DFunLike.congr_fun (LinearMap.congr_fun hh p) x⟩

/-- Characters detect the image of a homomorphism of abelian groups: an element lies in the image
exactly when every character vanishing on the image vanishes on it. -/
theorem _root_.AddMonoidHom.mem_range_iff_forall_characterModule {X Y : Type*} [AddCommGroup X]
    [AddCommGroup Y] (f : X →+ Y) (y : Y) :
    y ∈ f.range ↔ ∀ χ : CharacterModule Y, (∀ x, χ (f x) = 0) → χ y = 0 := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨x, rfl⟩ χ hχ
    exact hχ x
  rw [← QuotientAddGroup.eq_zero_iff]
  refine eq_zero_of_character_apply fun c ↦ ?_
  exact h (AddMonoidHom.comp c (QuotientAddGroup.mk' f.range)) fun x ↦
    (congrArg c ((QuotientAddGroup.eq_zero_iff (f x)).mpr
      (AddMonoidHom.mem_range.mpr ⟨x, rfl⟩))).trans (map_zero c)

/-- A finitely generated submodule `L` of a finite free module is a direct summand as soon as the
restriction of characters to `L` has an `Aᵐᵒᵖ`-linear section. -/
private theorem exists_comp_subtype_eq_id_of_section {n : ℕ} {L : Submodule A (Fin n → A)}
    (hL : L.FG) (σ : CharacterModule L →ₗ[Aᵐᵒᵖ] CharacterModule (Fin n → A))
    (hσ : ∀ (χ : CharacterModule L) (x : L), σ χ x = χ x) :
    ∃ φ : (Fin n → A) →ₗ[A] L, φ ∘ₗ L.subtype = LinearMap.id := by
  -- For generators `r i` of `L`, a retraction is a solution `y` in `L` of the finite linear system
  -- `∑ j, r i j • y j = r i`, and characters detect the solvability of such a system.
  obtain ⟨m, r, hr⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hL
  have hrL : ∀ i, r i ∈ L := fun i ↦ hr ▸ Submodule.subset_span ⟨i, rfl⟩
  let b : Fin m → L := fun i ↦ ⟨r i, hrL i⟩
  let Φ : (Fin n → L) →+ (Fin m → L) := AddMonoidHom.mk' (fun y i ↦ ∑ j, r i j • y j) fun y y' ↦ by
    funext i
    simp [Finset.sum_add_distrib]
  have hb : b ∈ Φ.range := (Φ.mem_range_iff_forall_characterModule b).mpr fun χ hχ ↦ by
    let c : Fin m → CharacterModule L :=
      fun i ↦ AddMonoidHom.comp χ (AddMonoidHom.single (fun _ ↦ L) i)
    have hc : ∀ j, ∑ i, op (r i j) • c i = 0 := fun j ↦ DFunLike.ext _ _ fun y ↦ by
      have hΦ : ∑ i, Pi.single i (r i j • y) = Φ (Pi.single j y) := by
        rw [Finset.univ_sum_single]
        funext i
        simp [Φ, Pi.single_apply, smul_ite]
      refine (AddMonoidHom.finsetSum_apply _ _ _).trans <|
        Eq.trans ?_ ((congrArg χ hΦ).trans (hχ _))
      rw [map_sum]
      rfl
    have hsum : ∀ i, c i (b i) = ∑ j, σ (op (r i j) • c i) (Pi.single j 1) := fun i ↦ by
      have hri : r i = ∑ j, r i j • (Pi.single j 1 : Fin n → A) := by
        funext k
        simp [Finset.sum_apply, Pi.single_apply]
      rw [← hσ, show ((b i : L) : Fin n → A) = r i from rfl, hri, map_sum]
      simp_rw [map_smul, mulOpposite_smul_apply, unop_op, ← hri]
    calc χ b = ∑ i, c i (b i) := by
          conv_lhs => rw [← Finset.univ_sum_single b, map_sum]
          rfl
      _ = ∑ j, σ (∑ i, op (r i j) • c i) (Pi.single j 1) := by
          simp_rw [hsum, map_sum]
          exact Finset.sum_comm.trans
            (Finset.sum_congr rfl fun _ _ ↦ (AddMonoidHom.finsetSum_apply _ _ _).symm)
      _ = 0 := Finset.sum_eq_zero fun j _ ↦ by
          rw [hc, map_zero]
          rfl
  obtain ⟨y, hy⟩ := hb
  let φ : (Fin n → A) →ₗ[A] L := Fintype.linearCombination A y
  refine ⟨φ, LinearMap.ext fun x ↦ Subtype.ext ?_⟩
  have hEq : Set.EqOn (L.subtype ∘ₗ φ) (LinearMap.id : (Fin n → A) →ₗ[A] _) (Set.range r) := by
    rintro _ ⟨i, rfl⟩
    have := congrArg Subtype.val (congrFun hy i)
    simpa [φ, Fintype.linearCombination_apply, Φ] using this
  exact LinearMap.eqOn_span hEq (hr ▸ x.2)

/-- **A finitely presented module with injective character module is projective.** -/
theorem projective_of_injective [Small.{v} A] [Module.FinitePresentation A M]
    [Module.Injective Aᵐᵒᵖ (CharacterModule M)] : Module.Projective A M := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A M
  have hex := LinearMap.exact_subtype_ker_map f
  have : Small.{v} Aᵐᵒᵖ := small_of_injective MulOpposite.unop_injective
  obtain ⟨ρ, hρ⟩ := Module.Injective.extension_property Aᵐᵒᵖ (CharacterModule M) _ _ (opDual f)
    (opDual_injective_of_surjective f hf) LinearMap.id
  have hdual := (Function.Exact.split_tfae' (exact_opDual hex)).out 2 1
  obtain ⟨-, σ, hσ⟩ := hdual.mp
    ⟨opDual_surjective_of_injective _ (Submodule.injective_subtype _), ρ, hρ⟩
  obtain ⟨φ, hφ⟩ := exists_comp_subtype_eq_id_of_section (Module.FinitePresentation.fg_ker f hf) σ
    fun χ x ↦ DFunLike.congr_fun (LinearMap.congr_fun hσ χ) x
  have hsplit := (Function.Exact.split_tfae' hex).out 2 1
  obtain ⟨-, s, hs⟩ := hsplit.mp ⟨hf, φ, hφ⟩
  exact Module.Projective.of_split s f hs

/-- A finitely presented module is projective exactly when its character module is injective. -/
theorem injective_iff_projective [Small.{v} A] [Module.FinitePresentation A M] :
    Module.Injective Aᵐᵒᵖ (CharacterModule M) ↔ Module.Projective A M :=
  ⟨fun _ ↦ projective_of_injective, fun _ ↦ injective_of_projective⟩

end CharacterModule
