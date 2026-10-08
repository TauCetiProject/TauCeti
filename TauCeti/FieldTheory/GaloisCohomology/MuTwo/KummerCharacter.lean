/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.SquareRoot
public import TauCeti.FieldTheory.GaloisCohomology.MuTwo.Basic
public import TauCeti.FieldTheory.GaloisCohomology.Restriction
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialF2.Character

/-!
# The Kummer class of a unit as the class of a character

Let `K` be a field and `G_K = AbsoluteGaloisGroup K`. For `r ∈ Kˢ` the sign `rootSign r g ∈ 𝔽₂`
records whether `g ∈ G_K` moves `r`. When `r² = b` lies in `K`, every `g` sends `r` to `±r`, so
`g ↦ rootSign r g` is a continuous homomorphism `G_K → 𝔽₂`, the **Kummer character** of `b`
(`TauCeti.kummerCharacter`). It is the Kummer cocycle `g ↦ g r / r ∈ μ₂` of
`TauCeti.kummerCocycleModTwo` read in `𝔽₂`, and when `2` is invertible in `K` the Kummer class
`(b) ∈ H¹(G_K, 𝔽₂)` is the class `TauCeti.ContCohomology.homClass` of this character
(`TauCeti.kummerClass_eq_homClass`). This pins the Kummer class at cochain level: an explicit
cocycle computation with Kummer classes, such as a cup product of two of them or an Evens norm,
can be carried out on the characters `rootSign r`.

For a finite extension `L/K` with an embedding `σ : L → Kˢ`, the same construction on the open
subgroup `G_L = galoisSubgroup K L σ` of `G_K` gives the Kummer character
`TauCeti.galoisKummerCharacter σ a r` of `a ∈ Lˣ`, for a square root `r` of `σ a`, and the Kummer
class of `a`, carried from `G_L` to `galoisSubgroup K L σ` by `TauCeti.galoisF2Iso`, is its class
(`TauCeti.galoisF2Iso_inv_kummerClass`).

## Main definitions

* `TauCeti.rootSign r g`: `0` when `g r = r` and `1` otherwise.
* `TauCeti.kummerCharacter b r hr`: the Kummer character `g ↦ rootSign r g` of `b = r²`.
* `TauCeti.galoisKummerCharacter σ a r hr`: the Kummer character of `a ∈ Lˣ` on
  `galoisSubgroup K L σ`, for `r² = σ a`.

## Main results

* `TauCeti.continuous_rootSign`, `TauCeti.continuous_kummerCharacter`,
  `TauCeti.continuous_galoisKummerCharacter`: the characters are continuous.
* `TauCeti.kummerClass_eq_homClass`: the Kummer class of `b` is the class of its Kummer character.
* `TauCeti.galoisF2Iso_inv_kummerClass`: the Kummer class of `a ∈ Lˣ`, carried to
  `galoisSubgroup K L σ`, is the class of its Kummer character there.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (6.2.1): the
  Kummer map sends `b` to the class of `g ↦ g r / r`.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory ContCohomology

universe u

variable {K : Type u} [Field K]

/-! ### The sign of a root -/

open Classical in
/-- **The sign of `r` under `g`**: `rootSign r g` is `0` when `g` fixes `r` and `1` otherwise.
When `r ≠ 0`, `r² ∈ K`, and `2` is invertible in `K`, it is the Kummer cocycle
`g ↦ g r / r ∈ μ₂` read in `𝔽₂`. -/
def rootSign (r : SeparableClosure K) (g : AbsoluteGaloisGroup K) : ZMod 2 :=
  if g r = r then 0 else 1

/-- The sign of a root that `g` fixes is `0`. -/
@[simp]
theorem rootSign_of_apply_eq {r : SeparableClosure K} {g : AbsoluteGaloisGroup K}
    (h : g r = r) : rootSign r g = 0 := by
  simp [rootSign, h]

/-- The sign of a root that `g` moves is `1`. -/
@[simp]
theorem rootSign_of_apply_ne {r : SeparableClosure K} {g : AbsoluteGaloisGroup K}
    (h : g r ≠ r) : rootSign r g = 1 := by
  simp [rootSign, h]

/-- The sign of `r` under `g` vanishes exactly when `g` fixes `r`. -/
@[simp]
theorem rootSign_eq_zero_iff {r : SeparableClosure K} {g : AbsoluteGaloisGroup K} :
    rootSign r g = 0 ↔ g r = r := by
  by_cases h : g r = r
  · simp [h]
  · simp [h]

/-- The sign of `r` under `g` is `1` exactly when `g` moves `r`. -/
@[simp]
theorem rootSign_eq_one_iff {r : SeparableClosure K} {g : AbsoluteGaloisGroup K} :
    rootSign r g = 1 ↔ g r ≠ r := by
  by_cases h : g r = r
  · simp [h]
  · simp [h]

/-- The sign of `r` under the identity is `0`. -/
@[simp]
theorem rootSign_one (r : SeparableClosure K) : rootSign r 1 = 0 :=
  rootSign_of_apply_eq rfl

/-- An element sending `r` to `±r` acts on `r` by the sign `(-1) ^ rootSign r g`. -/
theorem apply_eq_neg_one_pow_rootSign_mul {r : SeparableClosure K} {g : AbsoluteGaloisGroup K}
    (hg : g r = r ∨ g r = -r) : g r = (-1) ^ (rootSign r g).val * r := by
  by_cases h : g r = r
  · simp [h]
  · rw [rootSign_of_apply_ne h, ZMod.val_one, pow_one, neg_one_mul, hg.resolve_left h]

/-- **The sign of a root is additive** on the elements that send `r` to `±r`. -/
theorem rootSign_mul {r : SeparableClosure K} {g h : AbsoluteGaloisGroup K}
    (hg : g r = r ∨ g r = -r) (hh : h r = r ∨ h r = -r) :
    rootSign r (g * h) = rootSign r g + rootSign r h := by
  have hgh : (g * h) r = g (h r) := rfl
  by_cases hhr : h r = r
  · rw [rootSign_of_apply_eq hhr, add_zero]
    unfold rootSign
    rw [hgh, hhr]
  · have hhn : h r = -r := hh.resolve_left hhr
    rw [rootSign_of_apply_ne hhr]
    by_cases hgr : g r = r
    · rw [rootSign_of_apply_eq hgr, zero_add, rootSign_of_apply_ne]
      rwa [hgh, hhn, map_neg, hgr, ← hhn]
    · rw [rootSign_of_apply_ne hgr, rootSign_of_apply_eq]
      · decide
      · rw [hgh, hhn, map_neg, hg.resolve_left hgr, neg_neg]

/-- **The sign of a root is continuous**: its fibres are the stabilizer of `r`, which is open for
the Krull topology, and its complement. -/
theorem continuous_rootSign (r : SeparableClosure K) : Continuous (rootSign r) := by
  have hS := stabilizer_isOpen_of_isIntegral (K := K) r
  have hS' := (Subgroup.isClosed_of_isOpen _ hS).isOpen_compl
  rw [continuous_discrete_rng]
  intro b
  have hZ : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hZ b with rfl | rfl
  · convert hS using 1
    ext g
    simp [rootSign_eq_zero_iff]
  · convert hS' using 1
    ext g
    simp [rootSign_eq_one_iff]

/-! ### The Kummer character of a unit -/

/-- **The Kummer character of `b ∈ Kˣ`**, `g ↦ rootSign r g` for a square root `r` of `b` in
`Kˢ`. It is a homomorphism because every `g` sends `r` to `±r`. -/
def kummerCharacter (b : Kˣ) (r : SeparableClosure K)
    (hr : r ^ 2 = algebraMap K (SeparableClosure K) b) :
    AbsoluteGaloisGroup K →* Multiplicative (ZMod 2) where
  toFun g := Multiplicative.ofAdd (rootSign r g)
  map_one' := by simp
  map_mul' g h := by
    rw [rootSign_mul (g.apply_eq_or_eq_neg_of_sq_eq hr) (h.apply_eq_or_eq_neg_of_sq_eq hr),
      ofAdd_add]

/-- The value of the Kummer character at `g` is the sign of `r` under `g`. -/
@[simp]
theorem toAdd_kummerCharacter (b : Kˣ) (r : SeparableClosure K)
    (hr : r ^ 2 = algebraMap K (SeparableClosure K) b) (g : AbsoluteGaloisGroup K) :
    Multiplicative.toAdd (kummerCharacter b r hr g) = rootSign r g :=
  (rfl)

/-- The Kummer character is continuous: the stabilizer of `r` is open. -/
theorem continuous_kummerCharacter (b : Kˣ) (r : SeparableClosure K)
    (hr : r ^ 2 = algebraMap K (SeparableClosure K) b) :
    Continuous (kummerCharacter b r hr) :=
  continuous_ofAdd.comp (continuous_rootSign r)

/-- **The Kummer class is the class of the Kummer character.** If `r² = b`, the Kummer class
`(b) ∈ H¹(G_K, 𝔽₂)` is the class of the continuous homomorphism `g ↦ rootSign r g`. -/
theorem kummerClass_eq_homClass [Invertible (2 : K)] (b : Kˣ) (r : SeparableClosure K)
    (hr : r ^ 2 = algebraMap K (SeparableClosure K) b) :
    kummerClass b =
      homClass (AbsoluteGaloisGroup K) (kummerCharacter b r hr)
        (continuous_kummerCharacter b r hr) := by
  have hr0 : r ≠ 0 := by
    rintro rfl
    refine b.ne_zero ((algebraMap K (SeparableClosure K)).injective ?_)
    rw [map_zero, ← hr, zero_pow two_ne_zero]
  let α : (SeparableClosure K)ˣ := Units.mk0 r hr0
  have hα : α ^ 2 = Units.map (algebraMap K (SeparableClosure K)).toMonoidHom b :=
    Units.ext (by simpa [α] using hr)
  -- The Kummer cocycle of `α`, decoded in `ZMod 2`, is the Kummer character.
  have hc : ∀ g, ((kummerCocycleModTwo K hα : _ → _) g) =
      (trivialF2Equiv (AbsoluteGaloisGroup K)).symm
        (Multiplicative.toAdd (kummerCharacter b r hr g)) := fun g => by
    rw [AddEquiv.eq_symm_apply, kummerCocycleModTwo_apply, toAdd_kummerCharacter]
    by_cases hg : g r = r
    · have hgα : g • α = α := Units.ext (by simpa [α] using hg)
      simp [rootSign_of_apply_eq hg, hgα]
    · simp only [rootSign_of_apply_ne hg, ite_eq_right_iff, zero_ne_one, imp_false]
      exact fun h => hg (by simpa [α] using congrArg Units.val h)
  rw [kummerClass_eq_kummerCocycleModTwoClass_of_sq_eq K b α hα, kummerCocycleModTwoClass_def,
    eqToHom_explicitH1AddEquivContinuousCohomology_eq_cochainClass _
      (fun g => Multiplicative.toAdd (kummerCharacter b r hr g))
      (continuous_toAdd.comp (continuous_kummerCharacter b r hr)) hc, homClass_eq_cochainClass]

/-! ### The Kummer character over a finite extension -/

variable {L : Type u} [Field L] [Algebra K L] [FiniteDimensional K L]

/-- Every element of `galoisSubgroup K L σ` sends a square root of `σ a` to `±` itself. -/
theorem apply_eq_or_eq_neg_of_sq_eq_galoisSubgroup (σ : L →ₐ[K] SeparableClosure K) {a : L}
    {r : SeparableClosure K} (hr : r ^ 2 = σ a) (γ : (galoisSubgroup K L σ).toSubgroup) :
    (γ : AbsoluteGaloisGroup K) r = r ∨ (γ : AbsoluteGaloisGroup K) r = -r :=
  sq_eq_sq_iff_eq_or_eq_neg.1 <| by
    rw [← map_pow, hr]
    exact (mem_galoisSubgroup_iff K L σ).1 γ.2 a

/-- An element of `G_L = galoisSubgroup K L σ` acts on the Kummer coordinate `σ(y) r` through the
sign of `r`, for a square root `r` of `σ a`. -/
theorem apply_mul_eq_neg_one_pow_rootSign_mul (σ : L →ₐ[K] SeparableClosure K) {a : L}
    {r : SeparableClosure K} (hr : r ^ 2 = σ a) (y : L) {q : AbsoluteGaloisGroup K}
    (hq : q ∈ galoisSubgroup K L σ) :
    q (σ y * r) = (-1) ^ (rootSign r q).val * (σ y * r) := by
  rw [map_mul, (mem_galoisSubgroup_iff K L σ).1 hq y,
    apply_eq_neg_one_pow_rootSign_mul (apply_eq_or_eq_neg_of_sq_eq_galoisSubgroup σ hr ⟨q, hq⟩)]
  ring

/-- **The Kummer character of `a ∈ Lˣ` on `G_L = galoisSubgroup K L σ`**, `γ ↦ rootSign r γ` for a
square root `r` of `σ a`: every `γ` in `G_L` fixes `σ L`, hence `r²`, so `γ r = ±r`. -/
def galoisKummerCharacter (σ : L →ₐ[K] SeparableClosure K) (a : Lˣ) (r : SeparableClosure K)
    (hr : r ^ 2 = σ (a : L)) :
    (galoisSubgroup K L σ).toSubgroup →* Multiplicative (ZMod 2) where
  toFun γ := Multiplicative.ofAdd (rootSign r (γ : AbsoluteGaloisGroup K))
  map_one' := by simp
  map_mul' γ γ' := by
    rw [Subgroup.coe_mul, rootSign_mul (apply_eq_or_eq_neg_of_sq_eq_galoisSubgroup σ hr γ)
      (apply_eq_or_eq_neg_of_sq_eq_galoisSubgroup σ hr γ'), ofAdd_add]

/-- The value of the Kummer character of `a` at `γ` is the sign of `r` under `γ`. -/
@[simp]
theorem toAdd_galoisKummerCharacter (σ : L →ₐ[K] SeparableClosure K) (a : Lˣ)
    (r : SeparableClosure K) (hr : r ^ 2 = σ (a : L)) (γ : (galoisSubgroup K L σ).toSubgroup) :
    Multiplicative.toAdd (galoisKummerCharacter σ a r hr γ) =
      rootSign r (γ : AbsoluteGaloisGroup K) :=
  (rfl)

/-- The Kummer character of `a` on `G_L` is continuous. -/
theorem continuous_galoisKummerCharacter (σ : L →ₐ[K] SeparableClosure K) (a : Lˣ)
    (r : SeparableClosure K) (hr : r ^ 2 = σ (a : L)) :
    Continuous (galoisKummerCharacter σ a r hr) :=
  continuous_ofAdd.comp ((continuous_rootSign r).comp continuous_subtype_val)

/-- **The Kummer class of `a ∈ Lˣ`, carried to `galoisSubgroup K L σ`, is the class of its Kummer
character**: for a square root `r` of `σ a`, the transported class is represented by the character
`γ ↦ rootSign r γ`. -/
theorem galoisF2Iso_inv_kummerClass [Invertible (2 : L)] (σ : L →ₐ[K] SeparableClosure K)
    (a : Lˣ) (r : SeparableClosure K) (hr : r ^ 2 = σ (a : L)) :
    (galoisF2Iso K L σ 1).inv (kummerClass a) =
      homClass _ (galoisKummerCharacter σ a r hr) (continuous_galoisKummerCharacter σ a r hr) := by
  -- Apply the character comparison over `L`, then transport it along the subgroup equivalence.
  let e := separableClosureRingEquiv K L σ
  have hr' : e.symm r ^ 2 = algebraMap L (SeparableClosure L) a := by
    rw [← map_pow, hr, separableClosureRingEquiv_symm_apply_eq_algebraMap]
  rw [kummerClass_eq_homClass a (e.symm r) hr', galoisF2Iso_inv, trivialF2Map_homClass]
  congr 1
  ext γ
  rw [MonoidHom.comp_apply, toAdd_kummerCharacter, toAdd_galoisKummerCharacter]
  -- `γ` moves `r` exactly when its transport to `G_L` moves the corresponding root `e⁻¹ r`.
  have key : ((ContinuousMonoidHom.toContinuousMonoidHom (galoisSubgroupEquiv K L σ).symm :
      _ →* AbsoluteGaloisGroup L) γ) (e.symm r) = e.symm ((γ : AbsoluteGaloisGroup K) r) := by
    simp [e]
  by_cases hγ : (γ : AbsoluteGaloisGroup K) r = r
  · rw [rootSign_of_apply_eq hγ, rootSign_of_apply_eq (by rw [key, hγ])]
  · rw [rootSign_of_apply_ne hγ, rootSign_of_apply_ne (by rwa [key, e.symm.injective.ne_iff])]

end TauCeti
