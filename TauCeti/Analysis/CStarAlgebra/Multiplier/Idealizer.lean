/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Multiplier.Nondegenerate
public import TauCeti.Topology.Algebra.Star.Idealizer
import TauCeti.Analysis.CStarAlgebra.Ideal
import TauCeti.Analysis.CStarAlgebra.Quotient

/-!
# Essential-ideal universal property and concrete idealizer models of multiplier algebras

This file establishes two structural characterizations of the multiplier algebra `𝓜(ℂ, A)` of a
C⋆-algebra (complementing `DoubleCentralizer.ofUnitalAlgEquiv`,
`DoubleCentralizer.ofUnitalStarAlgEquiv`, `DoubleCentralizer.ofUnitalLinearIsometryEquiv`, and the
canonical essential ideal `DoubleCentralizer.coeTwoSidedIdeal` in
`TauCeti.Analysis.Normed.Algebra.DoubleCentralizer`):

1. **Universal property among essential ideal extensions**
   (`NonUnitalStarAlgHom.idealToMultiplier`).
   Any injective `ι : A →⋆ₙₐ[ℂ] D` whose range absorbs left multiplication induces a
   unique `ι.idealToMultiplier hι hmul : D →⋆ₙₐ[ℂ] 𝓜(ℂ, A)` extending `coe`, injective iff `ι(A)`
   has zero left annihilator in `D` (`idealToMultiplier_injective_iff`,
   `idealToMultiplier_injective_iff_forall_twoSidedIdeal`).
2. **Concrete idealizer models (`extendToMultiplierIdealizerEquiv`, `multiplierIdealizerEquiv`).**
   Any injective `ι : A →⋆ₙₐ[ℂ] D` into a unital C⋆-algebra induces
   `ι.idealizerToMultiplier hι : ι.range.idealizer →⋆ₐ[ℂ] 𝓜(ℂ, A)`. For injective nondegenerate
   `φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)` or `π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)`, this gives `⋆`-isomorphisms
   `𝓜(ℂ, A) ≃⋆ₐ[ℂ] φ.range.idealizer` and `𝓜(ℂ, A) ≃⋆ₐ[ℂ] π.range.idealizer`.

## References

* Bruce Blackadar, *Operator Algebras: Theory of C\*-Algebras and von Neumann Algebras*,
  Theorems II.7.3.1 and II.7.3.4.
* Gerd K. Pedersen, *C\*-Algebras and their Automorphism Groups*, Proposition 3.12.3.
* Iain Raeburn and Dana Williams, *Morita Equivalence and Continuous-Trace C\*-Algebras*,
  Propositions 2.50 and 2.54.
-/

public section

noncomputable section

open scoped MultiplierAlgebra

namespace NonUnitalStarAlgHom

/-! ### Universal property among ideal extensions (Blackadar II.7.3.1) -/

section IdealToMultiplier

variable {A D : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra D] (ι : A →⋆ₙₐ[ℂ] D)

/-- **Universal property of `𝓜(ℂ, A)` for ideal extensions.** Given an injective `⋆`-homomorphism
`ι : A →⋆ₙₐ[ℂ] D` between C⋆-algebras whose range absorbs left multiplication by `D`, there is a
canonical `⋆`-homomorphism `D →⋆ₙₐ[ℂ] 𝓜(ℂ, A)` sending `d : D` to the multiplier determined by
`ι (m.fst a) = d * ι a` and `ι (m.snd a) = ι a * d`. -/
def idealToMultiplier (hι : Function.Injective ι)
    (hmul : ∀ (d : D) (a : A), d * ι a ∈ Set.range ι) : D →⋆ₙₐ[ℂ] 𝓜(ℂ, A) :=
  (DoubleCentralizer.congr (StarAlgEquiv.ofInjective' ι hι).symm).toNonUnitalStarAlgHom.comp
    (ι.range.multiplierHom fun d _ ⟨a, ha⟩ => ha ▸ hmul d a)

variable {ι}

@[simp] theorem map_idealToMultiplier_fst (hι : Function.Injective ι)
    (hmul : ∀ (d : D) (a : A), d * ι a ∈ Set.range ι) (d : D) (a : A) :
    ι ((ι.idealToMultiplier hι hmul d).fst a) = d * ι a := by
  rw [← StarAlgEquiv.ofInjective'_apply ι hι ((ι.idealToMultiplier hι hmul d).fst a),
    idealToMultiplier, NonUnitalStarAlgHom.comp_apply, StarAlgEquiv.toNonUnitalStarAlgHom_apply,
    DoubleCentralizer.congr_apply_fst, StarAlgEquiv.symm_symm, StarAlgEquiv.apply_symm_apply,
    ι.range.coe_multiplierHom_fst_apply, StarAlgEquiv.ofInjective'_apply]

@[simp] theorem map_idealToMultiplier_snd (hι : Function.Injective ι)
    (hmul : ∀ (d : D) (a : A), d * ι a ∈ Set.range ι) (d : D) (a : A) :
    ι ((ι.idealToMultiplier hι hmul d).snd a) = ι a * d := by
  rw [← StarAlgEquiv.ofInjective'_apply ι hι ((ι.idealToMultiplier hι hmul d).snd a),
    idealToMultiplier, NonUnitalStarAlgHom.comp_apply, StarAlgEquiv.toNonUnitalStarAlgHom_apply,
    DoubleCentralizer.congr_apply_snd, StarAlgEquiv.symm_symm, StarAlgEquiv.apply_symm_apply,
    ι.range.coe_multiplierHom_snd_apply, StarAlgEquiv.ofInjective'_apply]

/-- `ι.idealToMultiplier hι hmul` restricts along `ι` to the canonical inclusion `A → 𝓜(ℂ, A)`. -/
@[simp] theorem idealToMultiplier_apply_map (hι : Function.Injective ι)
    (hmul : ∀ (d : D) (a : A), d * ι a ∈ Set.range ι) (a : A) :
    ι.idealToMultiplier hι hmul (ι a) = (a : 𝓜(ℂ, A)) :=
  DoubleCentralizer.ext_fst fun b => hι <| by
    rw [ι.map_idealToMultiplier_fst hι hmul, DoubleCentralizer.coe_fst,
      ContinuousLinearMap.mul_apply', map_mul]

@[simp] theorem idealToMultiplier_comp (hι : Function.Injective ι)
    (hmul : ∀ (d : D) (a : A), d * ι a ∈ Set.range ι) :
    (ι.idealToMultiplier hι hmul).comp ι = DoubleCentralizer.coeHom :=
  NonUnitalStarAlgHom.ext (ι.idealToMultiplier_apply_map hι hmul)

theorem eq_idealToMultiplier_iff (hι : Function.Injective ι)
    (hmul : ∀ (d : D) (a : A), d * ι a ∈ Set.range ι) {d : D} {m : 𝓜(ℂ, A)} :
    m = ι.idealToMultiplier hι hmul d ↔ ∀ a : A, ι (m.fst a) = d * ι a :=
  ⟨fun h a => h ▸ ι.map_idealToMultiplier_fst hι hmul d a,
    fun h => DoubleCentralizer.ext_fst fun a =>
      hι ((h a).trans (ι.map_idealToMultiplier_fst hι hmul d a).symm)⟩

/-- **Uniqueness in the universal property of `𝓜(ℂ, A)`.** `ι.idealToMultiplier hι hmul` is the
unique multiplicative map `D → 𝓜(ℂ, A)` extending the canonical inclusion along `ι`. -/
theorem eq_idealToMultiplier_of_apply (hι : Function.Injective ι)
    (hmul : ∀ (d : D) (a : A), d * ι a ∈ Set.range ι) {F : Type*} [FunLike F D 𝓜(ℂ, A)]
    [MulHomClass F D 𝓜(ℂ, A)] (ψ : F) (hψ : ∀ a : A, ψ (ι a) = (a : 𝓜(ℂ, A))) :
    ⇑ψ = ι.idealToMultiplier hι hmul := by
  funext d
  refine (ι.eq_idealToMultiplier_iff hι hmul).mpr fun a => ?_
  obtain ⟨b, hb⟩ := hmul d a
  have hmul_eq : ψ d * (a : 𝓜(ℂ, A)) = (b : 𝓜(ℂ, A)) := by rw [← hψ a, ← map_mul, ← hb, hψ b]
  rw [DoubleCentralizer.mul_coe_eq_coe_fst, DoubleCentralizer.coe_inj] at hmul_eq
  rw [hmul_eq, hb]

theorem idealToMultiplier_eq_zero_iff (hι : Function.Injective ι)
    (hmul : ∀ (d : D) (a : A), d * ι a ∈ Set.range ι) {d : D} :
    ι.idealToMultiplier hι hmul d = 0 ↔ ∀ a : A, d * ι a = 0 := by
  rw [eq_comm, ι.eq_idealToMultiplier_iff hι hmul]
  simp_rw [DoubleCentralizer.zero_fst, _root_.zero_apply, map_zero, eq_comm]

/-- **Essentiality criterion (Blackadar II.7.3.1).** `ι.idealToMultiplier hι hmul` is injective iff
the image of `ι` has zero left annihilator in `D`. -/
theorem idealToMultiplier_injective_iff (hι : Function.Injective ι)
    (hmul : ∀ (d : D) (a : A), d * ι a ∈ Set.range ι) :
    Function.Injective (ι.idealToMultiplier hι hmul) ↔
      ∀ d : D, (∀ a : A, d * ι a = 0) → d = 0 :=
  (injective_iff_map_eq_zero _).trans <|
    forall_congr' fun _ => imp_congr_left (ι.idealToMultiplier_eq_zero_iff hι hmul)

/-- **Ideal-intersection form of Blackadar II.7.3.1.** `ι.idealToMultiplier hι hmul` is injective if
and only if every two-sided ideal of `D` having trivial preimage under `ι` is zero. -/
theorem idealToMultiplier_injective_iff_forall_twoSidedIdeal (hι : Function.Injective ι)
    (hmul : ∀ (d : D) (a : A), d * ι a ∈ Set.range ι) :
    Function.Injective (ι.idealToMultiplier hι hmul) ↔
      ∀ J : TwoSidedIdeal D, (∀ a : A, ι a ∈ J → a = 0) → J = ⊥ := by
  rw [ι.idealToMultiplier_injective_iff hι hmul]
  refine ⟨fun h J hJ => eq_bot_iff.mpr fun d hd => ?_, fun h d hd => ?_⟩
  · rw [TwoSidedIdeal.mem_bot]
    refine h d fun a => ?_
    obtain ⟨b, hb⟩ := hmul d a
    rw [← hb, hJ b (hb ▸ J.mul_mem_right d (ι a) hd), map_zero]
  · let J : TwoSidedIdeal D := TwoSidedIdeal.mk' {x : D | ∀ a : A, x * ι a = 0}
      (fun a => zero_mul (ι a)) (fun {x y} hx hy a => by rw [add_mul, hx a, hy a, add_zero])
      (fun {x} hx a => by rw [neg_mul, hx a, neg_zero])
      (fun {x y} hy a => by rw [mul_assoc, hy a, mul_zero])
      (fun {x y} hx a => by obtain ⟨b, hb⟩ := hmul y a; rw [mul_assoc, ← hb, hx b])
    have hmem (x : D) : x ∈ J ↔ ∀ a : A, x * ι a = 0 := TwoSidedIdeal.mem_mk' _ _ _ _ _ _ x
    have hJ : J = ⊥ := h J fun a ha => mul_star_self_eq_zero.mp <|
      (map_eq_zero_iff ι hι).mp ((map_mul ι a (star a)).trans ((hmem (ι a)).mp ha (star a)))
    have hdJ : d ∈ J := (hmem d).mpr hd
    rwa [hJ, TwoSidedIdeal.mem_bot] at hdJ

end IdealToMultiplier

/-! ### Concrete idealizer homomorphisms and isomorphisms -/

section Idealizer

variable {A B D : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [CStarAlgebra D]

private def codRestrictIdealizer (ι : A →⋆ₙₐ[ℂ] D) : A →⋆ₙₐ[ℂ] ι.range.idealizer :=
  ι.codRestrict ι.range.idealizer.toNonUnitalStarSubalgebra
    fun a => ι.range.le_idealizer (ι.mem_range_self a)

private theorem codRestrictIdealizer_injective {ι : A →⋆ₙₐ[ℂ] D} (hι : Function.Injective ι) :
    Function.Injective (codRestrictIdealizer ι) := fun _ _ h => hι (congrArg Subtype.val h)

private theorem mul_codRestrictIdealizer_mem_range (ι : A →⋆ₙₐ[ℂ] D) (d : ι.range.idealizer)
    (a : A) : d * codRestrictIdealizer ι a ∈ Set.range (codRestrictIdealizer ι) :=
  let ⟨c, hc⟩ := ι.range.mul_mem_of_mem_idealizer_left d.property (ι.mem_range_self a)
  ⟨c, Subtype.ext hc⟩

/-- Any injective `⋆`-homomorphism `ι : A →⋆ₙₐ[ℂ] D` into a unital C⋆-algebra `D` induces a
canonical unital `⋆`-homomorphism from the idealizer `ι.range.idealizer` into `𝓜(ℂ, A)`. -/
def idealizerToMultiplier (ι : A →⋆ₙₐ[ℂ] D) (hι : Function.Injective ι) :
    ι.range.idealizer →⋆ₐ[ℂ] 𝓜(ℂ, A) :=
  let ψ := (codRestrictIdealizer ι).idealToMultiplier (codRestrictIdealizer_injective hι)
    (mul_codRestrictIdealizer_mem_range ι)
  have h1 : ψ 1 = 1 := DoubleCentralizer.ext_fst fun _ =>
    codRestrictIdealizer_injective hι (by simp [ψ])
  { __ := ψ
    map_one' := h1
    commutes' c := by
      rw [NonUnitalAlgHom.toFun_eq_coe, NonUnitalStarAlgHom.coe_toNonUnitalAlgHom,
        Algebra.algebraMap_eq_smul_one, map_smul, h1, Algebra.algebraMap_eq_smul_one] }

@[simp] theorem map_idealizerToMultiplier_fst {ι : A →⋆ₙₐ[ℂ] D} (hι : Function.Injective ι)
    (d : ι.range.idealizer) (a : A) : ι ((ι.idealizerToMultiplier hι d).fst a) = (d : D) * ι a :=
  congrArg Subtype.val <| (codRestrictIdealizer ι).map_idealToMultiplier_fst
    (codRestrictIdealizer_injective hι) (mul_codRestrictIdealizer_mem_range ι) d a

@[simp] theorem map_idealizerToMultiplier_snd {ι : A →⋆ₙₐ[ℂ] D} (hι : Function.Injective ι)
    (d : ι.range.idealizer) (a : A) : ι ((ι.idealizerToMultiplier hι d).snd a) = ι a * (d : D) :=
  congrArg Subtype.val <| (codRestrictIdealizer ι).map_idealToMultiplier_snd
    (codRestrictIdealizer_injective hι) (mul_codRestrictIdealizer_mem_range ι) d a

@[simp] theorem idealizerToMultiplier_apply_map {ι : A →⋆ₙₐ[ℂ] D} (hι : Function.Injective ι)
    (a : A) :
    ι.idealizerToMultiplier hι ⟨ι a, ι.range.le_idealizer (ι.mem_range_self a)⟩ = (a : 𝓜(ℂ, A)) :=
  DoubleCentralizer.ext_fst fun b => hι <| by
    rw [map_idealizerToMultiplier_fst, DoubleCentralizer.coe_fst,
      ContinuousLinearMap.mul_apply', map_mul]

/-- Every multiplier extension `φ.extendToMultiplier hφ m` lies in the idealizer of `φ.range`. -/
theorem extendToMultiplier_mem_idealizer {φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)}
    (hφ : φ.IsMultiplierNondegenerate) (m : 𝓜(ℂ, A)) :
    φ.extendToMultiplier hφ m ∈ φ.range.idealizer := by
  rw [φ.range.mem_idealizer]; rintro _ ⟨a, rfl⟩
  exact ⟨⟨m.fst a, (φ.extendToMultiplier_mul_eq_fst hφ m a).symm⟩,
    ⟨m.snd a, (φ.mul_extendToMultiplier_eq_snd hφ m a).symm⟩⟩

/-- **Concrete idealizer isomorphism in `𝓜(ℂ, B)`.** An injective multiplier-nondegenerate
`⋆`-homomorphism `φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)` identifies `𝓜(ℂ, A)` with `φ.range.idealizer`. -/
def extendToMultiplierIdealizerEquiv {φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)} (hφ : φ.IsMultiplierNondegenerate)
    (hφ_inj : Function.Injective φ) : 𝓜(ℂ, A) ≃⋆ₐ[ℂ] φ.range.idealizer :=
  let f := (φ.extendToMultiplier hφ).codRestrict φ.range.idealizer
    (φ.extendToMultiplier_mem_idealizer hφ)
  { __ := f
    invFun := φ.idealizerToMultiplier hφ_inj
    left_inv m := DoubleCentralizer.ext_fst fun a => hφ_inj (by simp [f])
    right_inv d := Subtype.ext <| hφ.ext fun a => by simp [f]
    map_smul' := map_smul f }

@[simp] theorem coe_extendToMultiplierIdealizerEquiv_apply {φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)}
    (hφ : φ.IsMultiplierNondegenerate) (hφ_inj : Function.Injective φ) (m : 𝓜(ℂ, A)) :
    (φ.extendToMultiplierIdealizerEquiv hφ hφ_inj m : 𝓜(ℂ, B)) = φ.extendToMultiplier hφ m := (rfl)

@[simp] theorem extendToMultiplierIdealizerEquiv_symm_apply {φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)}
    (hφ : φ.IsMultiplierNondegenerate) (hφ_inj : Function.Injective φ) (d : φ.range.idealizer) :
    (φ.extendToMultiplierIdealizerEquiv hφ hφ_inj).symm d = φ.idealizerToMultiplier hφ_inj d :=
  (rfl)

/-- If `φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)` is injective and multiplier-nondegenerate, `φ.extendToMultiplier hφ`
is injective. -/
theorem extendToMultiplier_injective {φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)} (hφ : φ.IsMultiplierNondegenerate)
    (hφ_inj : Function.Injective φ) : Function.Injective (φ.extendToMultiplier hφ) :=
  fun _ _ h => (φ.extendToMultiplierIdealizerEquiv hφ hφ_inj).injective (Subtype.ext h)

/-- If `φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)` is injective and multiplier-nondegenerate, the range of
`φ.extendToMultiplier hφ` is `φ.range.idealizer`. -/
@[simp] theorem range_extendToMultiplier_eq_idealizer {φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)}
    (hφ : φ.IsMultiplierNondegenerate) (hφ_inj : Function.Injective φ) :
    (φ.extendToMultiplier hφ).range = φ.range.idealizer :=
  le_antisymm (by rintro _ ⟨x, rfl⟩; exact φ.extendToMultiplier_mem_idealizer hφ x) fun m hm =>
    ⟨(φ.extendToMultiplierIdealizerEquiv hφ hφ_inj).symm ⟨m, hm⟩, congrArg Subtype.val
      ((φ.extendToMultiplierIdealizerEquiv hφ hφ_inj).apply_symm_apply ⟨m, hm⟩)⟩

section HilbertSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every Hilbert-space multiplier extension `π.multiplierExtension hπ m` lies in the idealizer of
`π.range`. -/
theorem multiplierExtension_mem_idealizer {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)} (hπ : π.IsNondegenerate)
    (m : 𝓜(ℂ, A)) : π.multiplierExtension hπ m ∈ π.range.idealizer := by
  rw [π.range.mem_idealizer]; rintro _ ⟨a, rfl⟩
  exact ⟨⟨m.fst a, (π.multiplierExtension_mul_eq_fst hπ m a).symm⟩,
    ⟨m.snd a, (π.mul_multiplierExtension_eq_snd hπ m a).symm⟩⟩

/-- **Concrete idealizer isomorphism in `B(H)` (Blackadar II.7.3.4).** A faithful nondegenerate
Hilbert-space representation `π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)` identifies `𝓜(ℂ, A)` with
`π.range.idealizer`. -/
def multiplierIdealizerEquiv {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)} (hπ : π.IsNondegenerate)
    (hπ_inj : Function.Injective π) : 𝓜(ℂ, A) ≃⋆ₐ[ℂ] π.range.idealizer :=
  let f := (π.multiplierExtension hπ).codRestrict π.range.idealizer
    (π.multiplierExtension_mem_idealizer hπ)
  { __ := f
    invFun := π.idealizerToMultiplier hπ_inj
    left_inv m := DoubleCentralizer.ext_fst fun a => hπ_inj (by simp [f])
    right_inv d := Subtype.ext <| hπ.ext fun a => by simp [f]
    map_smul' := map_smul f }

@[simp] theorem coe_multiplierIdealizerEquiv_apply {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    (hπ : π.IsNondegenerate) (hπ_inj : Function.Injective π) (m : 𝓜(ℂ, A)) :
    (π.multiplierIdealizerEquiv hπ hπ_inj m : H →L[ℂ] H) = π.multiplierExtension hπ m := (rfl)

@[simp] theorem multiplierIdealizerEquiv_symm_apply {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    (hπ : π.IsNondegenerate) (hπ_inj : Function.Injective π) (d : π.range.idealizer) :
    (π.multiplierIdealizerEquiv hπ hπ_inj).symm d = π.idealizerToMultiplier hπ_inj d := (rfl)

/-- If `π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)` is faithful and nondegenerate, `π.multiplierExtension hπ` is
injective. -/
theorem multiplierExtension_injective {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)} (hπ : π.IsNondegenerate)
    (hπ_inj : Function.Injective π) : Function.Injective (π.multiplierExtension hπ) :=
  fun _ _ h => (π.multiplierIdealizerEquiv hπ hπ_inj).injective (Subtype.ext h)

/-- If `π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)` is faithful and nondegenerate, the range of
`π.multiplierExtension hπ` is `π.range.idealizer`. -/
@[simp] theorem range_multiplierExtension_eq_idealizer {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    (hπ : π.IsNondegenerate) (hπ_inj : Function.Injective π) :
    (π.multiplierExtension hπ).range = π.range.idealizer :=
  le_antisymm (by rintro _ ⟨x, rfl⟩; exact π.multiplierExtension_mem_idealizer hπ x) fun T hT =>
    ⟨(π.multiplierIdealizerEquiv hπ hπ_inj).symm ⟨T, hT⟩, congrArg Subtype.val
      ((π.multiplierIdealizerEquiv hπ hπ_inj).apply_symm_apply ⟨T, hT⟩)⟩

end HilbertSpace

end Idealizer

end NonUnitalStarAlgHom

end
