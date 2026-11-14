/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Multiplier

/-!
# Continuous central multiplier cocycles of C⋆-actions

For a point-norm continuous action `α` of a topological group `G` on a possibly nonunital complex
C⋆-algebra `A`, a *normalized continuous central `α`-cocycle* (`CentralCocycle α`) is a map
`ω : G → G → unitary 𝓜(ℂ, A)` taking values in the unitary center of the multiplier algebra
`𝓜(ℂ, A)`, normalized by `ω(1, s) = ω(s, 1) = 1`, satisfying the `2`-cocycle identity
`α'_r(ω(s, t)) * ω(r, s * t) = ω(r, s) * ω(r * s, t)` for the induced multiplier action
`α' = α.multiplier`, and strictly continuous in the sense that both `(s, t) ↦ ω(s, t) a` and
`(s, t) ↦ a ω(s, t)` are norm-continuous for every `a : A`.

Because `ω(s, t)` is central in `𝓜(ℂ, A)`, its left and right centralizers agree on `A`
(`CentralCocycle.fst_eq_snd`), and `α` remains an honest group action rather than a Busby–Smith
twisted action. Pointwise multiplication in `unitary 𝓜(ℂ, A)` equips `CentralCocycle α` with an
abelian group structure (`CommGroup`), where `1` is the trivial cocycle and `(ω⁻¹)(s, t)` is
`star (ω(s, t))`. Because unitary multipliers have norm at most `1` (including on the zero
algebra), pointwise strict continuity upgrades to joint norm continuity of `(s, t, a) ↦ ω(s, t) a`
and `(s, t, a) ↦ a ω(s, t)`.

Central cocycles pull back along continuous group homomorphisms (`CentralCocycle.comp`,
`CentralCocycle.compHom`), transport along `⋆`-isomorphisms of coefficient algebras
(`CentralCocycle.conjugate`, `CentralCocycle.conjugateEquiv`), and include continuous normalized
`unitary ℂ`-valued scalar `2`-cocycles acting through scalar multipliers (`CentralCocycle.scalar`).

## Main definitions

* `TauCeti.CStarAction.CentralCocycle`: normalized strictly continuous central multiplier
  `2`-cocycles of `α`, carrying a `CommGroup` structure.
* `TauCeti.CStarAction.CentralCocycle.comp`, `TauCeti.CStarAction.CentralCocycle.compHom`:
  pullback along a `ContinuousMonoidHom`.
* `TauCeti.CStarAction.CentralCocycle.conjugate`,
  `TauCeti.CStarAction.CentralCocycle.conjugateEquiv`: transport along a `StarAlgEquiv`.
* `TauCeti.CStarAction.CentralCocycle.scalar`: central multiplier cocycle attached to a continuous
  normalized `unitary ℂ`-valued `2`-cocycle.

## Main statements

* `TauCeti.CStarAction.CentralCocycle.fst_eq_snd`: left and right actions of `ω(s, t)` on `A`
  coincide.
* `TauCeti.CStarAction.CentralCocycle.multiplier_value_mul_value`: the cocycle identity in
  `𝓜(ℂ, A)`.
* `TauCeti.CStarAction.CentralCocycle.multiplier_value_inv_left`: `α'_s(ω(s⁻¹, s)) = ω(s, s⁻¹)`.
* `TauCeti.CStarAction.CentralCocycle.continuous_fst_apply`,
  `TauCeti.CStarAction.CentralCocycle.continuous_snd_apply`: joint continuity with varying
  `A`-valued arguments.

## References

* Judith A. Packer and Iain Raeburn, *Twisted crossed products of C*-algebras*, Math. Proc.
  Cambridge Philos. Soc. 106 (1989), 293–311, Section 1, specialized to honest actions with
  central multiplier twists.
* Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2, for the induced action on
  multiplier algebras and its strict continuity.
-/

public section

noncomputable section

open scoped MultiplierAlgebra

namespace TauCeti.CStarAction

variable {G A : Type*} [Group G] [TopologicalSpace G] [NonUnitalCStarAlgebra A]

/-- A normalized continuous central `α`-cocycle with values in the unitary center of the
multiplier algebra `𝓜(ℂ, A)`. Strict continuity is expressed through the left and right
centralizer actions on `A`, and the cocycle law
`α'_r(ω(s, t)) * ω(r, s * t) = ω(r, s) * ω(r * s, t)` is stated on left actions. -/
structure CentralCocycle (α : CStarAction G A) where
  /-- The unitary multiplier values of the cocycle. -/
  value : G → G → unitary 𝓜(ℂ, A)
  /-- Centrality in the multiplier algebra. -/
  central : ∀ s t (m : 𝓜(ℂ, A)), Commute (value s t : 𝓜(ℂ, A)) m
  /-- Normalization at the identity on the left. -/
  one_left : ∀ s, value 1 s = 1
  /-- Normalization at the identity on the right. -/
  one_right : ∀ s, value s 1 = 1
  /-- The `2`-cocycle identity on left actions. -/
  cocycle : ∀ r s t (a : A),
    α r ((value s t : 𝓜(ℂ, A)).fst ((α r).symm ((value r (s * t) : 𝓜(ℂ, A)).fst a))) =
      (value r s : 𝓜(ℂ, A)).fst ((value (r * s) t : 𝓜(ℂ, A)).fst a)
  /-- Joint norm continuity of `(s, t) ↦ ω(s, t) a` for each fixed `a : A`. -/
  strict_left : ∀ a : A, Continuous fun q : G × G => (value q.1 q.2 : 𝓜(ℂ, A)).fst a
  /-- Joint norm continuity of `(s, t) ↦ a ω(s, t)` for each fixed `a : A`. -/
  strict_right : ∀ a : A, Continuous fun q : G × G => (value q.1 q.2 : 𝓜(ℂ, A)).snd a

namespace CentralCocycle

variable {α : CStarAction G A}

attribute [simp] one_left one_right

/-- A central cocycle is determined by its values on pairs of group elements. -/
@[ext]
theorem ext {ω₁ ω₂ : CentralCocycle α} (h : ∀ s t, ω₁.value s t = ω₂.value s t) : ω₁ = ω₂ := by
  cases ω₁
  cases ω₂
  have hval : _ = _ := funext₂ h
  subst hval
  rfl

/-- Every value of a central cocycle lies in the center of `𝓜(ℂ, A)`. -/
theorem value_mem_center (ω : CentralCocycle α) (s t : G) :
    (ω.value s t : 𝓜(ℂ, A)) ∈ Subring.center 𝓜(ℂ, A) :=
  Subring.mem_center_iff.2 fun m => (ω.central s t m).symm

/-- Because `ω(s, t)` is central, its left and right centralizers agree on `A`. -/
theorem fst_eq_snd (ω : CentralCocycle α) (s t : G) (a : A) :
    (ω.value s t : 𝓜(ℂ, A)).fst a = (ω.value s t : 𝓜(ℂ, A)).snd a :=
  DoubleCentralizer.forall_commute_iff_fst_eq_snd.1 (ω.central s t) a

/-- The adjoint of a central multiplier is again central. -/
theorem commute_star_value (ω : CentralCocycle α) (s t : G) (m : 𝓜(ℂ, A)) :
    Commute (star (ω.value s t : 𝓜(ℂ, A))) m := by
  rw [commute_iff_eq, ← star_star m, ← star_mul, ← star_mul, (ω.central s t (star m)).eq]

/-- The image of a cocycle value under `α.multiplier` remains central in `𝓜(ℂ, A)`. -/
theorem commute_multiplier_value (ω : CentralCocycle α) (r s t : G) (m : 𝓜(ℂ, A)) :
    Commute (α.multiplier r (ω.value s t : 𝓜(ℂ, A))) m := by
  have h := (ω.central s t ((α.multiplier r).symm m)).map (α.multiplier r)
  rwa [StarAlgEquiv.apply_symm_apply] at h

/-- The image of a starred cocycle value under `α.multiplier` remains central in `𝓜(ℂ, A)`. -/
theorem commute_multiplier_star_value (ω : CentralCocycle α) (r s t : G) (m : 𝓜(ℂ, A)) :
    Commute (α.multiplier r (star (ω.value s t : 𝓜(ℂ, A)))) m := by
  have h := (ω.commute_star_value s t ((α.multiplier r).symm m)).map (α.multiplier r)
  rwa [StarAlgEquiv.apply_symm_apply] at h

/-- The `2`-cocycle identity in the multiplier algebra `𝓜(ℂ, A)`:
`α'_r(ω(s, t)) * ω(r, s * t) = ω(r, s) * ω(r * s, t)`. -/
theorem multiplier_value_mul_value (ω : CentralCocycle α) (r s t : G) :
    α.multiplier r (ω.value s t : 𝓜(ℂ, A)) * (ω.value r (s * t) : 𝓜(ℂ, A)) =
      (ω.value r s : 𝓜(ℂ, A)) * (ω.value (r * s) t : 𝓜(ℂ, A)) := by
  refine DoubleCentralizer.ext_fst fun a => ?_
  simpa [DoubleCentralizer.mul_fst, mul_apply_eq_comp] using ω.cocycle r s t a

/-- Evaluating the cocycle identity at `(s, s⁻¹, s)` gives `α'_s(ω(s⁻¹, s)) = ω(s, s⁻¹)`. -/
theorem multiplier_value_inv_left (ω : CentralCocycle α) (s : G) :
    α.multiplier s (ω.value s⁻¹ s : 𝓜(ℂ, A)) = (ω.value s s⁻¹ : 𝓜(ℂ, A)) := by
  simpa using ω.multiplier_value_mul_value s s⁻¹ s

/-- Applying `α'_s⁻¹` to `multiplier_value_inv_left` gives `α'_s⁻¹(ω(s, s⁻¹)) = ω(s⁻¹, s)`. -/
theorem multiplier_inv_value_inv_right (ω : CentralCocycle α) (s : G) :
    α.multiplier s⁻¹ (ω.value s s⁻¹ : 𝓜(ℂ, A)) = (ω.value s⁻¹ s : 𝓜(ℂ, A)) := by
  rw [← multiplier_symm_apply, StarAlgEquiv.symm_apply_eq, ω.multiplier_value_inv_left]

/-! ### Joint continuity with varying coefficients -/

/-- Joint norm continuity of `(q, a) ↦ ω(q.1, q.2) a` on `(G × G) × A`. -/
theorem continuous_prod_fst (ω : CentralCocycle α) :
    Continuous fun p : (G × G) × A => (ω.value p.1.1 p.1.2 : 𝓜(ℂ, A)).fst p.2 :=
  DoubleCentralizer.continuous_fst_of_opNorm_le (𝕜 := ℂ)
    (m := fun q : G × G => (ω.value q.1 q.2 : 𝓜(ℂ, A)))
    (fun q => DoubleCentralizer.norm_unitary_fst_le_one (ω.value q.1 q.2)) ω.strict_left

/-- Joint norm continuity of `(q, a) ↦ a ω(q.1, q.2)` on `(G × G) × A`. -/
theorem continuous_prod_snd (ω : CentralCocycle α) :
    Continuous fun p : (G × G) × A => (ω.value p.1.1 p.1.2 : 𝓜(ℂ, A)).snd p.2 :=
  DoubleCentralizer.continuous_snd_of_opNorm_le (𝕜 := ℂ)
    (m := fun q : G × G => (ω.value q.1 q.2 : 𝓜(ℂ, A)))
    (fun q => DoubleCentralizer.norm_unitary_snd_le_one (ω.value q.1 q.2)) ω.strict_right

/-- Continuity of `x ↦ ω(s x, t x) (a x)` for continuously varying arguments. -/
@[fun_prop]
theorem continuous_fst_apply (ω : CentralCocycle α) {X : Type*} [TopologicalSpace X]
    {s t : X → G} {a : X → A} (hs : Continuous s) (ht : Continuous t) (ha : Continuous a) :
    Continuous fun x => (ω.value (s x) (t x) : 𝓜(ℂ, A)).fst (a x) :=
  ω.continuous_prod_fst.comp ((hs.prodMk ht).prodMk ha)

/-- Continuity of `x ↦ (a x) ω(s x, t x)` for continuously varying arguments. -/
@[fun_prop]
theorem continuous_snd_apply (ω : CentralCocycle α) {X : Type*} [TopologicalSpace X]
    {s t : X → G} {a : X → A} (hs : Continuous s) (ht : Continuous t) (ha : Continuous a) :
    Continuous fun x => (ω.value (s x) (t x) : 𝓜(ℂ, A)).snd (a x) :=
  ω.continuous_prod_snd.comp ((hs.prodMk ht).prodMk ha)

/-! ### Abelian group structure -/

instance : One (CentralCocycle α) where
  one :=
    { value _ _ := 1
      central _ _ := Commute.one_left
      one_left _ := rfl
      one_right _ := rfl
      cocycle _ _ _ _ := by simp
      strict_left _ := by simpa using continuous_const
      strict_right _ := by simpa using continuous_const }

@[simp]
theorem one_value (s t : G) : (1 : CentralCocycle α).value s t = 1 :=
  (rfl)

instance : Mul (CentralCocycle α) where
  mul ω₁ ω₂ :=
    { value s t := ω₁.value s t * ω₂.value s t
      central s t m := (ω₁.central s t m).mul_left (ω₂.central s t m)
      one_left s := by simp
      one_right s := by simp
      cocycle r s t a := by
        have hmul :
            α.multiplier r ((ω₁.value s t * ω₂.value s t : unitary 𝓜(ℂ, A)) : 𝓜(ℂ, A)) *
                ((ω₁.value r (s * t) * ω₂.value r (s * t) : unitary 𝓜(ℂ, A)) : 𝓜(ℂ, A)) =
              ((ω₁.value r s * ω₂.value r s : unitary 𝓜(ℂ, A)) : 𝓜(ℂ, A)) *
                ((ω₁.value (r * s) t * ω₂.value (r * s) t : unitary 𝓜(ℂ, A)) : 𝓜(ℂ, A)) := by
          push_cast
          rw [map_mul]
          calc α.multiplier r (ω₁.value s t : 𝓜(ℂ, A)) * α.multiplier r (ω₂.value s t : 𝓜(ℂ, A)) *
                ((ω₁.value r (s * t) : 𝓜(ℂ, A)) * (ω₂.value r (s * t) : 𝓜(ℂ, A)))
              = (α.multiplier r (ω₁.value s t : 𝓜(ℂ, A)) * (ω₁.value r (s * t) : 𝓜(ℂ, A))) *
                  (α.multiplier r (ω₂.value s t : 𝓜(ℂ, A)) * (ω₂.value r (s * t) : 𝓜(ℂ, A))) := by
                simp only [mul_assoc]
                congr 1
                rw [← mul_assoc, (ω₁.central r (s * t) _).symm.eq, mul_assoc]
            _ = ((ω₁.value r s : 𝓜(ℂ, A)) * (ω₁.value (r * s) t : 𝓜(ℂ, A))) *
                  ((ω₂.value r s : 𝓜(ℂ, A)) * (ω₂.value (r * s) t : 𝓜(ℂ, A))) := by
                rw [ω₁.multiplier_value_mul_value, ω₂.multiplier_value_mul_value]
            _ = (ω₁.value r s : 𝓜(ℂ, A)) * (ω₂.value r s : 𝓜(ℂ, A)) *
                  ((ω₁.value (r * s) t : 𝓜(ℂ, A)) * (ω₂.value (r * s) t : 𝓜(ℂ, A))) := by
                simp only [mul_assoc]
                congr 1
                rw [← mul_assoc, (ω₁.central (r * s) t _).eq, mul_assoc]
        simpa [DoubleCentralizer.mul_fst, mul_apply_eq_comp] using congr(($hmul).fst a)
      strict_left a := by
        simp only [Submonoid.coe_mul, DoubleCentralizer.mul_fst, mul_apply_eq_comp]
        exact ω₁.continuous_fst_apply continuous_fst continuous_snd (ω₂.strict_left a)
      strict_right a := by
        simp only [Submonoid.coe_mul, DoubleCentralizer.mul_snd, mul_apply_eq_comp]
        exact ω₂.continuous_snd_apply continuous_fst continuous_snd (ω₁.strict_right a) }

@[simp]
theorem mul_value (ω₁ ω₂ : CentralCocycle α) (s t : G) :
    (ω₁ * ω₂).value s t = ω₁.value s t * ω₂.value s t :=
  (rfl)

instance : Inv (CentralCocycle α) where
  inv ω :=
    { value s t := (ω.value s t)⁻¹
      central s t m := by
        rw [← Unitary.star_eq_inv, Unitary.coe_star]
        exact ω.commute_star_value s t m
      one_left s := by simp
      one_right s := by simp
      cocycle r s t a := by
        have hinv :
            α.multiplier r (((ω.value s t)⁻¹ : unitary 𝓜(ℂ, A)) : 𝓜(ℂ, A)) *
                (((ω.value r (s * t))⁻¹ : unitary 𝓜(ℂ, A)) : 𝓜(ℂ, A)) =
              (((ω.value r s)⁻¹ : unitary 𝓜(ℂ, A)) : 𝓜(ℂ, A)) *
                (((ω.value (r * s) t)⁻¹ : unitary 𝓜(ℂ, A)) : 𝓜(ℂ, A)) := by
          simp only [← Unitary.star_eq_inv, Unitary.coe_star, map_star]
          rw [(ω.commute_star_value r (s * t) _).symm.eq, ← star_mul,
            ω.multiplier_value_mul_value, star_mul, (ω.commute_star_value (r * s) t _).eq]
        simpa [DoubleCentralizer.mul_fst, mul_apply_eq_comp] using congr(($hinv).fst a)
      strict_left a := by
        simp only [← Unitary.star_eq_inv, Unitary.coe_star, DoubleCentralizer.star_fst]
        exact (ω.strict_right (star a)).star
      strict_right a := by
        simp only [← Unitary.star_eq_inv, Unitary.coe_star, DoubleCentralizer.star_snd]
        exact (ω.strict_left (star a)).star }

@[simp]
theorem inv_value (ω : CentralCocycle α) (s t : G) :
    ω⁻¹.value s t = (ω.value s t)⁻¹ :=
  (rfl)

/-- In `𝓜(ℂ, A)`, the value of `ω⁻¹` at `(s, t)` is the adjoint `star (ω.value s t)`. -/
theorem coe_inv_value (ω : CentralCocycle α) (s t : G) :
    (ω⁻¹.value s t : 𝓜(ℂ, A)) = star (ω.value s t : 𝓜(ℂ, A)) := by
  rw [inv_value, ← Unitary.star_eq_inv, Unitary.coe_star]

instance : Div (CentralCocycle α) where
  div ω₁ ω₂ := ω₁ * ω₂⁻¹

@[simp]
theorem div_value (ω₁ ω₂ : CentralCocycle α) (s t : G) :
    (ω₁ / ω₂).value s t = ω₁.value s t / ω₂.value s t :=
  (div_eq_mul_inv (ω₁.value s t) (ω₂.value s t)).symm

instance : Pow (CentralCocycle α) ℕ where
  pow ω n := npowRec n ω

instance : Pow (CentralCocycle α) ℤ where
  pow ω n := zpowRec npowRec n ω

instance : CommGroup (CentralCocycle α) where
  mul_assoc _ _ _ := ext fun _ _ => mul_assoc _ _ _
  one_mul _ := ext fun _ _ => one_mul _
  mul_one _ := ext fun _ _ => mul_one _
  inv_mul_cancel _ := ext fun _ _ => inv_mul_cancel _
  div_eq_mul_inv _ _ := rfl
  npow n ω := ω ^ n
  zpow n ω := ω ^ n
  mul_comm ω₁ ω₂ := ext fun s t => Subtype.ext (ω₁.central s t (ω₂.value s t : 𝓜(ℂ, A))).eq

/-! ### Pullback and conjugacy transport -/

section Functoriality

variable {H K B C : Type*} [Group H] [TopologicalSpace H] [Group K] [TopologicalSpace K]
  [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]

/-- Pull back a central cocycle along a continuous group homomorphism. -/
def comp (ω : CentralCocycle α) (φ : ContinuousMonoidHom H G) : CentralCocycle (α.comp φ) where
  value h₁ h₂ := ω.value (φ h₁) (φ h₂)
  central h₁ h₂ := ω.central (φ h₁) (φ h₂)
  one_left h := by simp
  one_right h := by simp
  cocycle r s t a := by simpa [map_mul] using ω.cocycle (φ r) (φ s) (φ t) a
  strict_left a := (ω.strict_left a).comp (φ.continuous.prodMap φ.continuous)
  strict_right a := (ω.strict_right a).comp (φ.continuous.prodMap φ.continuous)

@[simp]
theorem comp_value (ω : CentralCocycle α) (φ : ContinuousMonoidHom H G) (h₁ h₂ : H) :
    (ω.comp φ).value h₁ h₂ = ω.value (φ h₁) (φ h₂) :=
  (rfl)

/-- Pullback of central cocycles along a continuous group homomorphism, as a group homomorphism. -/
def compHom (α : CStarAction G A) (φ : ContinuousMonoidHom H G) :
    CentralCocycle α →* CentralCocycle (α.comp φ) where
  toFun ω := ω.comp φ
  map_one' := ext fun _ _ => rfl
  map_mul' _ _ := ext fun _ _ => rfl

@[simp]
theorem compHom_apply (ω : CentralCocycle α) (φ : ContinuousMonoidHom H G) :
    compHom α φ ω = ω.comp φ :=
  (rfl)

/-- Transport a central cocycle along a `⋆`-algebra isomorphism `e : A ≃⋆ₐ[ℂ] B` of coefficient
algebras. -/
def conjugate (ω : CentralCocycle α) (e : A ≃⋆ₐ[ℂ] B) : CentralCocycle (α.conjugate e) where
  value s t := Unitary.map (StarMonoidHom.ofClass (DoubleCentralizer.congr e)) (ω.value s t)
  central s t m := by
    have h := (ω.central s t ((DoubleCentralizer.congr e).symm m)).map (DoubleCentralizer.congr e)
    rwa [StarAlgEquiv.apply_symm_apply] at h
  one_left s := Subtype.ext (by simp)
  one_right s := Subtype.ext (by simp)
  cocycle r s t b := by
    simp only [Unitary.coe_map, StarMonoidHom.ofClass_coe, DoubleCentralizer.congr_apply_fst,
      conjugate_apply, StarAlgEquiv.symm_apply_apply]
    simpa [StarAlgEquiv.symm_apply_apply] using congr(e $(ω.cocycle r s t (e.symm b)))
  strict_left b := by
    simp only [Unitary.coe_map, StarMonoidHom.ofClass_coe, DoubleCentralizer.congr_apply_fst]
    exact (StarAlgEquiv.isometry e).continuous.comp (ω.strict_left (e.symm b))
  strict_right b := by
    simp only [Unitary.coe_map, StarMonoidHom.ofClass_coe, DoubleCentralizer.congr_apply_snd]
    exact (StarAlgEquiv.isometry e).continuous.comp (ω.strict_right (e.symm b))

@[simp]
theorem coe_conjugate_value (ω : CentralCocycle α) (e : A ≃⋆ₐ[ℂ] B) (s t : G) :
    ((ω.conjugate e).value s t : 𝓜(ℂ, B)) = DoubleCentralizer.congr e (ω.value s t : 𝓜(ℂ, A)) :=
  (rfl)

/-- Left centralizer action of a transported central cocycle. -/
theorem conjugate_fst (ω : CentralCocycle α) (e : A ≃⋆ₐ[ℂ] B) (s t : G) (b : B) :
    ((ω.conjugate e).value s t : 𝓜(ℂ, B)).fst b =
      e ((ω.value s t : 𝓜(ℂ, A)).fst (e.symm b)) := by
  simp

/-- Right centralizer action of a transported central cocycle. -/
theorem conjugate_snd (ω : CentralCocycle α) (e : A ≃⋆ₐ[ℂ] B) (s t : G) (b : B) :
    ((ω.conjugate e).value s t : 𝓜(ℂ, B)).snd b =
      e ((ω.value s t : 𝓜(ℂ, A)).snd (e.symm b)) := by
  simp

/-- Transport of central cocycles along `e : A ≃⋆ₐ[ℂ] B`, as a multiplicative isomorphism. -/
def conjugateEquiv (α : CStarAction G A) (e : A ≃⋆ₐ[ℂ] B) :
    CentralCocycle α ≃* CentralCocycle (α.conjugate e) where
  toFun ω := ω.conjugate e
  invFun ω' :=
    { value s t := Unitary.map (StarMonoidHom.ofClass (DoubleCentralizer.congr e.symm))
        (ω'.value s t)
      central s t m := by
        have h := (ω'.central s t ((DoubleCentralizer.congr e.symm).symm m)).map
          (DoubleCentralizer.congr e.symm)
        rwa [StarAlgEquiv.apply_symm_apply] at h
      one_left s := Subtype.ext (by simp)
      one_right s := Subtype.ext (by simp)
      cocycle r s t a := by
        have h := ω'.cocycle r s t (e a)
        simp only [conjugate_apply] at h
        simpa [Unitary.coe_map, StarMonoidHom.ofClass_coe, DoubleCentralizer.congr_apply_fst] using
          congr(e.symm $h)
      strict_left a := by
        simp only [Unitary.coe_map, StarMonoidHom.ofClass_coe, DoubleCentralizer.congr_apply_fst]
        exact (StarAlgEquiv.isometry e.symm).continuous.comp (ω'.strict_left (e a))
      strict_right a := by
        simp only [Unitary.coe_map, StarMonoidHom.ofClass_coe, DoubleCentralizer.congr_apply_snd]
        exact (StarAlgEquiv.isometry e.symm).continuous.comp (ω'.strict_right (e a)) }
  left_inv ω := ext fun s t => Subtype.ext <| DoubleCentralizer.ext_fst fun a => by simp
  right_inv ω' := ext fun s t => Subtype.ext <| DoubleCentralizer.ext_fst fun b => by simp
  map_mul' _ _ := ext fun _ _ => Subtype.ext <| by simp [map_mul]

@[simp]
theorem conjugateEquiv_apply (ω : CentralCocycle α) (e : A ≃⋆ₐ[ℂ] B) :
    conjugateEquiv α e ω = ω.conjugate e :=
  (rfl)

end Functoriality

/-! ### Scalar `unitary ℂ`-valued cocycles -/

/-- Every normalized continuous scalar `2`-cocycle `c : G → G → unitary ℂ` defines a normalized
continuous central `α`-cocycle `(s, t) ↦ c s t • 1` by scalar multiplication in `unitary 𝓜(ℂ, A)`,
for any action `α : CStarAction G A`. -/
def scalar (α : CStarAction G A) (c : G → G → unitary ℂ)
    (hone_left : ∀ s, c 1 s = 1) (hone_right : ∀ s, c s 1 = 1)
    (hcocycle : ∀ r s t, c s t * c r (s * t) = c r s * c (r * s) t)
    (hcont : Continuous (Function.uncurry c)) : CentralCocycle α where
  value s t := c s t • 1
  central s t m := by
    rw [Unitary.coe_smul, Submonoid.coe_one]
    exact (Commute.one_left m).smul_left (c s t : ℂ)
  one_left s := by simp [hone_left]
  one_right s := by simp [hone_right]
  cocycle r s t a := by
    have hc : (c r (s * t) : ℂ) * (c s t : ℂ) = (c (r * s) t : ℂ) * (c r s : ℂ) := by
      rw [mul_comm, mul_comm (c (r * s) t : ℂ)]
      simpa only [Submonoid.coe_mul] using congrArg Subtype.val (hcocycle r s t)
    simp [Submonoid.smul_def, map_smul, smul_smul, hc]
  strict_left a := by
    simp only [Unitary.coe_smul, Submonoid.coe_one, DoubleCentralizer.smul_fst,
      DoubleCentralizer.one_fst]
    exact (continuous_subtype_val.comp hcont).smul continuous_const
  strict_right a := by
    simp only [Unitary.coe_smul, Submonoid.coe_one, DoubleCentralizer.smul_snd,
      DoubleCentralizer.one_snd]
    exact (continuous_subtype_val.comp hcont).smul continuous_const

@[simp]
theorem scalar_value (α : CStarAction G A) (c : G → G → unitary ℂ)
    (hone_left : ∀ s, c 1 s = 1) (hone_right : ∀ s, c s 1 = 1)
    (hcocycle : ∀ r s t, c s t * c r (s * t) = c r s * c (r * s) t)
    (hcont : Continuous (Function.uncurry c)) (s t : G) :
    (scalar α c hone_left hone_right hcocycle hcont).value s t = c s t • 1 :=
  (rfl)

end CentralCocycle

end TauCeti.CStarAction
