/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.LocallyConvex.Basic
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic

/-!
# Extended Lipschitz seminorms

Let `E` be a real topological vector space with a distinguished element `e`, typically an
order-unit space with its order unit. An *extended Lipschitz seminorm* for `e` is a function
`L : E → ℝ≥0∞` which is subadditive and absolutely homogeneous, `L (r • a) = ‖r‖ₑ * L a` (with
`0 * ∞ = 0`), whose *finite domain* `{a | L a ≠ ∞}` is dense, and whose zero set is exactly the
scalar line `ℝ ∙ e`. Such seminorms are the input to Rieffel's metrics on state spaces: the
distance of two states `φ`, `ψ` is the supremum of `|φ a - ψ a|` over `L a ≤ 1`. The value `∞`
records the elements outside the domain on which the seminorm is naturally finite, such as the
non-Lipschitz functions in `C(X, ℝ)`.

## Main definitions

* `TauCeti.ExtendedLipschitzSeminorm e`: extended Lipschitz seminorms for `e`.
* `TauCeti.ExtendedLipschitzSeminorm.domain`: the finite domain, a dense real submodule
  containing `e`, and `TauCeti.ExtendedLipschitzSeminorm.toSeminorm`, the finite real seminorm
  on it.
* `TauCeti.ExtendedLipschitzSeminorm.ofSeminorm`: conversely, a real seminorm on a dense
  submodule containing `e` with kernel `ℝ ∙ e`, extended by `∞` outside that submodule. The two
  constructions are inverse to each other (`ofSeminorm_toSeminorm`, `domain_ofSeminorm`,
  `toSeminorm_ofSeminorm`).
* `TauCeti.ExtendedLipschitzSeminorm.smul`: rescaling by a nonzero `t : ℝ≥0`.
* `TauCeti.ExtendedLipschitzSeminorm.sup`: the maximum of two extended Lipschitz seminorms whose
  finite domains have dense intersection.
* `TauCeti.ExtendedLipschitzSeminorm.comap`: pullback along a linear map, and
  `TauCeti.ExtendedLipschitzSeminorm.comapEquiv`, transport along a continuous linear
  equivalence.

## Main statements

* `TauCeti.ExtendedLipschitzSeminorm.map_add_of_eq_zero` and `map_add_smul_self`: an extended
  Lipschitz seminorm is invariant under translation by its kernel, in particular by multiples of
  `e`.
* `TauCeti.ExtendedLipschitzSeminorm.convex_setOf_le` and `balanced_setOf_le`: its sublevel sets
  are convex and balanced.

## References

* M. A. Rieffel, *Metrics on state spaces*, Doc. Math. 4 (1999), §2.
* M. A. Rieffel, *Gromov–Hausdorff distance for quantum metric spaces*, Mem. Amer. Math. Soc.
  168 (2004), Definition 2.1.
-/

public section

open scoped ENNReal NNReal

namespace TauCeti

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- An **extended Lipschitz seminorm** for `e : E` on a real topological vector space `E`: a
subadditive, absolutely homogeneous function `L : E → ℝ≥0∞` whose finite domain
`{a | L a ≠ ∞}` is dense and whose zero set is exactly the scalar line `ℝ ∙ e`. -/
structure ExtendedLipschitzSeminorm (e : E) where
  /-- The underlying `ℝ≥0∞`-valued function. Use the coercion to a function instead. -/
  toFun : E → ℝ≥0∞
  map_add_le' (a b : E) : toFun (a + b) ≤ toFun a + toFun b
  map_smul' (r : ℝ) (a : E) : toFun (r • a) = ‖r‖ₑ * toFun a
  dense_ne_top' : Dense {a | toFun a ≠ ∞}
  eq_zero_iff' (a : E) : toFun a = 0 ↔ a ∈ ℝ ∙ e

namespace ExtendedLipschitzSeminorm

variable {e : E} (L M : ExtendedLipschitzSeminorm e) {a b : E}

instance : FunLike (ExtendedLipschitzSeminorm e) E ℝ≥0∞ where
  coe := toFun
  coe_injective L M h := by cases L; cases M; congr

@[simp]
theorem toFun_eq_coe : L.toFun = ⇑L := rfl

@[ext]
theorem ext {L M : ExtendedLipschitzSeminorm e} (h : ∀ a, L a = M a) : L = M :=
  DFunLike.ext _ _ h

theorem map_add_le (a b : E) : L (a + b) ≤ L a + L b :=
  L.map_add_le' a b

theorem map_smul_eq_mul (r : ℝ) (a : E) : L (r • a) = ‖r‖ₑ * L a :=
  L.map_smul' r a

theorem eq_zero_iff : L a = 0 ↔ a ∈ ℝ ∙ e :=
  L.eq_zero_iff' a

@[simp]
protected theorem map_zero : L 0 = 0 := by
  simpa using L.map_smul_eq_mul 0 0

@[simp]
protected theorem map_neg (a : E) : L (-a) = L a := by
  simpa using L.map_smul_eq_mul (-1) a

theorem map_sub_rev (a b : E) : L (a - b) = L (b - a) := by
  rw [← neg_sub, L.map_neg]

theorem map_sub_le (a b : E) : L (a - b) ≤ L a + L b := by
  simpa [sub_eq_add_neg] using L.map_add_le a (-b)

@[simp]
theorem map_smul_self (r : ℝ) : L (r • e) = 0 :=
  L.eq_zero_iff.2 (Submodule.smul_mem _ r (Submodule.mem_span_singleton_self e))

@[simp]
theorem map_self : L e = 0 := by
  simpa using L.map_smul_self 1

/-- An extended Lipschitz seminorm is invariant under translation by an element of its kernel. -/
theorem map_add_of_eq_zero (hb : L b = 0) : L (a + b) = L a :=
  le_antisymm (by simpa [hb] using L.map_add_le a b)
    (by simpa [hb] using L.map_add_le (a + b) (-b))

/-- **Scalar translation**: `L (a + r • e) = L a`. -/
@[simp]
theorem map_add_smul_self (a : E) (r : ℝ) : L (a + r • e) = L a :=
  L.map_add_of_eq_zero (L.map_smul_self r)

@[simp]
theorem map_sub_smul_self (a : E) (r : ℝ) : L (a - r • e) = L a := by
  rw [sub_eq_add_neg, ← neg_smul, L.map_add_smul_self]

/-! ### Sublevel sets -/

/-- The sublevel sets of an extended Lipschitz seminorm are convex. -/
theorem convex_setOf_le (c : ℝ≥0∞) : Convex ℝ {a | L a ≤ c} := by
  intro a ha b hb s t hs ht hst
  calc L (s • a + t • b) ≤ ENNReal.ofReal s * L a + ENNReal.ofReal t * L b := by
        simpa [L.map_smul_eq_mul, Real.eNorm_eq_ofReal, hs, ht] using
          L.map_add_le (s • a) (t • b)
    _ ≤ ENNReal.ofReal s * c + ENNReal.ofReal t * c := by gcongr <;> assumption
    _ = c := by rw [← add_mul, ← ENNReal.ofReal_add hs ht, hst, ENNReal.ofReal_one, one_mul]

/-- The sublevel sets of an extended Lipschitz seminorm are balanced. -/
theorem balanced_setOf_le (c : ℝ≥0∞) : Balanced ℝ {a | L a ≤ c} := by
  rintro r hr _ ⟨a, ha : L a ≤ c, rfl⟩
  calc L (r • a) = ‖r‖ₑ * L a := L.map_smul_eq_mul r a
    _ ≤ 1 * c := by
        gcongr
        rw [Real.eNorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_one.2 hr
    _ = c := one_mul c

/-! ### The order on extended Lipschitz seminorms -/

instance : PartialOrder (ExtendedLipschitzSeminorm e) :=
  PartialOrder.lift _ DFunLike.coe_injective

@[simp, norm_cast]
theorem coe_le_coe : ⇑L ≤ ⇑M ↔ L ≤ M :=
  Iff.rfl

theorem le_def : L ≤ M ↔ ∀ a, L a ≤ M a :=
  Iff.rfl

/-! ### The finite domain -/

/-- The **finite domain** `{a | L a ≠ ∞}` of an extended Lipschitz seminorm, as a real
submodule. -/
def domain : Submodule ℝ E where
  carrier := {a | L a ≠ ∞}
  add_mem' {a b} ha hb := ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ha, hb⟩) (L.map_add_le a b)
  zero_mem' := by simp
  smul_mem' r a ha := by
    simp only [Set.mem_ofPred_eq, L.map_smul_eq_mul] at ha ⊢
    exact ENNReal.mul_ne_top (by simp) ha

@[simp]
theorem mem_domain : a ∈ L.domain ↔ L a ≠ ∞ :=
  Iff.rfl

theorem dense_domain : Dense (L.domain : Set E) :=
  L.dense_ne_top'

theorem span_singleton_le_domain : ℝ ∙ e ≤ L.domain := fun a ha => by
  simp [L.eq_zero_iff.2 ha]

theorem self_mem_domain : e ∈ L.domain := by
  simp

variable {L M} in
theorem domain_anti (h : L ≤ M) : M.domain ≤ L.domain := fun _ ha =>
  ne_top_of_le_ne_top ha (h _)

/-- The finite real seminorm of an extended Lipschitz seminorm on its finite domain. -/
noncomputable def toSeminorm : Seminorm ℝ L.domain :=
  Seminorm.of (fun a => (L a).toReal)
    (fun a b => by
      rw [← ENNReal.toReal_add a.property b.property]
      exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨a.property, b.property⟩)
        (L.map_add_le a b))
    (fun r a => by simp [L.map_smul_eq_mul])

@[simp]
theorem toSeminorm_apply (a : L.domain) : L.toSeminorm a = (L a).toReal :=
  (rfl)

theorem ofReal_toSeminorm (a : L.domain) : ENNReal.ofReal (L.toSeminorm a) = L a :=
  ENNReal.ofReal_toReal a.property

theorem toSeminorm_eq_zero_iff (a : L.domain) : L.toSeminorm a = 0 ↔ (a : E) ∈ ℝ ∙ e := by
  simp [ENNReal.toReal_eq_zero_iff, L.mem_domain.1 a.property, L.eq_zero_iff]

/-! ### Extension of a seminorm by `∞` -/

section OfSeminorm

omit [TopologicalSpace E]

variable (D : Submodule ℝ E) (p : Seminorm ℝ D)

/-- The extension of a seminorm `p` on a submodule `D` by `∞` outside `D`. -/
private noncomputable def extendTop (a : E) : ℝ≥0∞ :=
  ⨅ h : a ∈ D, ENNReal.ofReal (p ⟨a, h⟩)

private theorem extendTop_of_mem (h : a ∈ D) : extendTop D p a = ENNReal.ofReal (p ⟨a, h⟩) :=
  iInf_pos h

private theorem extendTop_of_notMem (h : a ∉ D) : extendTop D p a = ∞ :=
  iInf_neg h

private theorem extendTop_ne_top_iff : extendTop D p a ≠ ∞ ↔ a ∈ D := by
  by_cases h : a ∈ D <;> simp [h, extendTop_of_mem, extendTop_of_notMem]

private theorem extendTop_add_le (a b : E) :
    extendTop D p (a + b) ≤ extendTop D p a + extendTop D p b := by
  by_cases ha : a ∈ D
  · by_cases hb : b ∈ D
    · rw [extendTop_of_mem D p ha, extendTop_of_mem D p hb,
        extendTop_of_mem D p (D.add_mem ha hb), ← ENNReal.ofReal_add (apply_nonneg _ _)
          (apply_nonneg _ _)]
      exact ENNReal.ofReal_le_ofReal (map_add_le_add p ⟨a, ha⟩ ⟨b, hb⟩)
    · simp [extendTop_of_notMem D p hb]
  · simp [extendTop_of_notMem D p ha]

private theorem extendTop_smul (r : ℝ) (a : E) :
    extendTop D p (r • a) = ‖r‖ₑ * extendTop D p a := by
  by_cases ha : a ∈ D
  · rw [extendTop_of_mem D p ha, extendTop_of_mem D p (D.smul_mem r ha),
      ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg r)]
    exact congrArg ENNReal.ofReal (SeminormClass.map_smul_eq_mul p r ⟨a, ha⟩)
  · rcases eq_or_ne r 0 with rfl | hr
    · simp [extendTop_of_mem D p D.zero_mem, (Submodule.mk_eq_zero D D.zero_mem).2 rfl]
    · rw [extendTop_of_notMem D p ha, extendTop_of_notMem D p fun h => ha (by
        simpa [hr] using D.smul_mem r⁻¹ h), ENNReal.mul_top (by simpa using hr)]

end OfSeminorm

/-- The extended Lipschitz seminorm obtained from a real seminorm `p` on a dense submodule `D`
containing `e`, with kernel `ℝ ∙ e`, by setting it to `∞` outside `D`. -/
noncomputable def ofSeminorm (D : Submodule ℝ E) (p : Seminorm ℝ D) (he : e ∈ D)
    (hD : Dense (D : Set E)) (hp : ∀ a : D, p a = 0 ↔ (a : E) ∈ ℝ ∙ e) :
    ExtendedLipschitzSeminorm e where
  toFun := extendTop D p
  map_add_le' := extendTop_add_le D p
  map_smul' := extendTop_smul D p
  dense_ne_top' := by simpa [extendTop_ne_top_iff] using hD
  eq_zero_iff' a := by
    by_cases ha : a ∈ D
    · rw [extendTop_of_mem D p ha, ENNReal.ofReal_eq_zero, ← hp ⟨a, ha⟩]
      exact (apply_nonneg p _).ge_iff_eq'
    · rw [extendTop_of_notMem D p ha]
      exact iff_of_false ENNReal.top_ne_zero fun h => ha
        ((Submodule.span_singleton_le_iff_mem e D).2 he h)

section OfSeminorm

variable {D : Submodule ℝ E} {p : Seminorm ℝ D} {he : e ∈ D} {hD : Dense (D : Set E)}
  {hp : ∀ a : D, p a = 0 ↔ (a : E) ∈ ℝ ∙ e}

theorem ofSeminorm_apply_of_mem (ha : a ∈ D) :
    ofSeminorm D p he hD hp a = ENNReal.ofReal (p ⟨a, ha⟩) :=
  extendTop_of_mem D p ha

theorem ofSeminorm_apply_of_notMem (ha : a ∉ D) : ofSeminorm D p he hD hp a = ∞ :=
  extendTop_of_notMem D p ha

@[simp]
theorem domain_ofSeminorm : (ofSeminorm D p he hD hp).domain = D :=
  Submodule.ext fun _ => extendTop_ne_top_iff D p

theorem toSeminorm_ofSeminorm (a : (ofSeminorm D p he hD hp).domain) :
    (ofSeminorm D p he hD hp).toSeminorm a = p ⟨a, by simpa using a.property⟩ := by
  simp [ofSeminorm_apply_of_mem (by simpa using a.property : (a : E) ∈ D)]

end OfSeminorm

/-- An extended Lipschitz seminorm is the extension by `∞` of its finite seminorm on its finite
domain. -/
@[simp]
theorem ofSeminorm_toSeminorm :
    ofSeminorm L.domain L.toSeminorm L.self_mem_domain L.dense_domain L.toSeminorm_eq_zero_iff =
      L :=
  ext fun a => by
    by_cases ha : a ∈ L.domain
    · rw [ofSeminorm_apply_of_mem ha, ofReal_toSeminorm]
    · simpa [ofSeminorm_apply_of_notMem ha, eq_comm] using ha

/-! ### Rescaling and maxima -/

/-- The rescaling `t * L` of an extended Lipschitz seminorm by a nonzero `t : ℝ≥0`. -/
noncomputable def smul (t : ℝ≥0) (ht : t ≠ 0) : ExtendedLipschitzSeminorm e where
  toFun a := t * L a
  map_add_le' a b := by
    rw [← mul_add]
    exact mul_le_mul_right (L.map_add_le a b) _
  map_smul' r a := by rw [L.map_smul_eq_mul, mul_left_comm]
  dense_ne_top' := L.dense_domain.mono fun a ha => by simpa [ENNReal.mul_eq_top, ht] using ha
  eq_zero_iff' a := by simp [ht, L.eq_zero_iff]

@[simp]
theorem smul_apply (t : ℝ≥0) (ht : t ≠ 0) (a : E) : L.smul t ht a = t * L a :=
  (rfl)

@[simp]
theorem domain_smul (t : ℝ≥0) (ht : t ≠ 0) : (L.smul t ht).domain = L.domain :=
  Submodule.ext fun a => by simp [ENNReal.mul_eq_top, ht]

/-- The maximum of two extended Lipschitz seminorms, provided their finite domains have dense
intersection. -/
def sup (h : Dense ((L.domain ⊓ M.domain : Submodule ℝ E) : Set E)) :
    ExtendedLipschitzSeminorm e where
  toFun a := max (L a) (M a)
  map_add_le' a b :=
    (max_le_max (L.map_add_le a b) (M.map_add_le a b)).trans max_add_add_le_max_add_max
  map_smul' r a := by rw [L.map_smul_eq_mul, M.map_smul_eq_mul, mul_max]
  dense_ne_top' := h.mono fun a ha => by simpa using ha
  eq_zero_iff' a := by simp [L.eq_zero_iff, M.eq_zero_iff]

section Sup

variable (h : Dense ((L.domain ⊓ M.domain : Submodule ℝ E) : Set E))

@[simp]
theorem sup_apply (a : E) : L.sup M h a = max (L a) (M a) :=
  (rfl)

@[simp]
theorem domain_sup : (L.sup M h).domain = L.domain ⊓ M.domain :=
  Submodule.ext fun a => by simp

protected theorem le_sup_left : L ≤ L.sup M h := fun a => le_max_left (L a) (M a)

protected theorem le_sup_right : M ≤ L.sup M h := fun a => le_max_right (L a) (M a)

/-- The maximum `L.sup M h` is the least extended Lipschitz seminorm above `L` and `M`. -/
protected theorem sup_le {N : ExtendedLipschitzSeminorm e} (hL : L ≤ N) (hM : M ≤ N) :
    L.sup M h ≤ N :=
  fun a => max_le (hL a) (hM a)

protected theorem sup_le_iff {N : ExtendedLipschitzSeminorm e} :
    L.sup M h ≤ N ↔ L ≤ N ∧ M ≤ N :=
  ⟨fun hN => ⟨(L.le_sup_left M h).trans hN, (L.le_sup_right M h).trans hN⟩,
    fun hLM => L.sup_le M h hLM.1 hLM.2⟩

end Sup

/-! ### Pullback and transport -/

variable [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] {f : F}

/-- The pullback `a ↦ L (T a)` of an extended Lipschitz seminorm along a linear map `T` sending
`f` to `e`, provided the kernel of `T` lies in `ℝ ∙ f` and the finite domain pulls back to a
dense set. For the inclusion of a subspace containing `e` this is the restriction of `L`. -/
def comap (T : F →ₗ[ℝ] E) (hT : T f = e) (hker : LinearMap.ker T ≤ ℝ ∙ f)
    (hdense : Dense (T ⁻¹' L.domain)) : ExtendedLipschitzSeminorm f where
  toFun a := L (T a)
  map_add_le' a b := by simpa using L.map_add_le (T a) (T b)
  map_smul' r a := by simpa using L.map_smul_eq_mul r (T a)
  dense_ne_top' := hdense
  eq_zero_iff' a := by
    refine L.eq_zero_iff.trans ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 h
      have hker' : a - r • f ∈ LinearMap.ker T := by simp [hr, hT]
      simpa using
        add_mem (hker hker') (Submodule.smul_mem _ r (Submodule.mem_span_singleton_self f))
    · obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 h
      simpa [hT] using Submodule.smul_mem _ r (Submodule.mem_span_singleton_self e)

@[simp]
theorem comap_apply (T : F →ₗ[ℝ] E) (hT : T f = e) (hker : LinearMap.ker T ≤ ℝ ∙ f)
    (hdense : Dense (T ⁻¹' L.domain)) (a : F) : L.comap T hT hker hdense a = L (T a) :=
  (rfl)

@[simp]
theorem domain_comap (T : F →ₗ[ℝ] E) (hT : T f = e) (hker : LinearMap.ker T ≤ ℝ ∙ f)
    (hdense : Dense (T ⁻¹' L.domain)) : (L.comap T hT hker hdense).domain = L.domain.comap T :=
  Submodule.ext fun _ => Iff.rfl

/-- The transport of an extended Lipschitz seminorm along a continuous linear equivalence
`T : F ≃L[ℝ] E` sending `f` to `e`. -/
def comapEquiv (T : F ≃L[ℝ] E) (hT : T f = e) : ExtendedLipschitzSeminorm f :=
  L.comap (T : F →ₗ[ℝ] E) hT ((LinearMap.ker_eq_bot.2 T.injective).trans_le bot_le)
    (L.dense_domain.preimage T.toHomeomorph.isOpenMap)

@[simp]
theorem comapEquiv_apply (T : F ≃L[ℝ] E) (hT : T f = e) (a : F) :
    L.comapEquiv T hT a = L (T a) :=
  (rfl)

end ExtendedLipschitzSeminorm

end TauCeti
