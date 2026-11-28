/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Induced
public import TauCeti.Algebra.MonoidAlgebra.CharacterTwist
public import TauCeti.RepresentationTheory.FiniteIndex
public import TauCeti.RepresentationTheory.WeilDeligne.Induction.Basic
public import TauCeti.RepresentationTheory.WeilDeligne.Special

/-!
# Induction of Weil–Deligne parameters in the tensor model

`TauCeti.WeilDeligneParameter.ind` induces a raw Weil–Deligne parameter `(V', r', N')` for `W'`
along `ι : W' →* W` on the function model, Mathlib's coinduced representation. This file puts the
monodromy on the tensor model, Mathlib's induced representation `Representation.ind ι r'` on
`IndV ι r' = (E[W] ⊗ V')_{W'}`, and compares the two.

In left-coset notation the tensor model is spanned by `g ⊗ v` with `w (g ⊗ v) = (w g) ⊗ v`, and
the induced monodromy is `N_Ind (g ⊗ v) = q ^ (-deg g) • g ⊗ N' v`. Mathlib writes the induced
representation with right translations: `h` acts on the class `⟦w ⊗ v⟧` by `⟦w h⁻¹ ⊗ v⟧`, so
`⟦w ⊗ v⟧` is `g ⊗ v` for `g = w⁻¹` (index inversion), and the monodromy becomes
`N ⟦w ⊗ v⟧ = q ^ deg w • ⟦w ⊗ N' v⟧` (`TauCeti.WeilDeligneParameter.indVN_mk`). On `E[W] ⊗ V'`
it is the twist `MonoidAlgebra.charTwist` of `E[W]` by the character
`ω(w) = q ^ deg w` (`TauCeti.WeilDeligneParameter.omega`) tensored with `N'`. It is well defined
on the coinvariants because `N' (r' g v) = (q ^ f) ^ (-deg' g) • r' g (N' v)` and
`deg (ι g) = f · deg' g`. It is nilpotent and satisfies the conjugation relation for `q` with
respect to `Representation.ind ι r'`.

For a subgroup `S ≤ W`, Mathlib's map `Rep.indToCoind` from the tensor model to the function model
intertwines this monodromy with the function-model monodromy
`TauCeti.WeilDeligneParameter.indN` (`TauCeti.WeilDeligneParameter.indToCoind_indVN`). When `S`
has finite index, `Rep.indToCoind` is an isomorphism (`Rep.indCoindIso`), so this is what is
needed to identify the two models of the induced parameter.

## Main definitions

* `TauCeti.WeilDeligneParameter.indVN`: the monodromy `⟦w ⊗ v⟧ ↦ q ^ deg w • ⟦w ⊗ N' v⟧` on the
  tensor model.

## Main results

* `TauCeti.WeilDeligneParameter.isNilpotent_indVN` and
  `TauCeti.WeilDeligneParameter.ind_mul_indVN_mul_ind_inv`: it is nilpotent and satisfies the
  conjugation relation for `q`.
* `TauCeti.WeilDeligneParameter.indToCoind_indVN`: Mathlib's comparison map from the tensor
  model to the function model intertwines the two monodromies.

## References

* P. Deligne, *Les constantes des équations fonctionnelles des fonctions L*, in *Modular functions
  of one variable II*, Lecture Notes in Math. 349 (1973), §8.4.1, p. 568.
-/

public section

noncomputable section

open scoped MonoidAlgebra

namespace TauCeti

namespace WeilDeligneParameter

open _root_.Representation

variable {E W W' V' : Type*} [Field E] [Group W] [Group W']
  [TopologicalSpace W'] [AddCommGroup V'] [Module E V']
  {deg : W →* Multiplicative ℤ} {deg' : W' →* Multiplicative ℤ} {q : ℕ}

variable (ι : W' →* W) (f : ℕ) (hf : ∀ w, (deg (ι w)).toAdd = f * (deg' w).toAdd)
  (hq : (q : E) ≠ 0)

include hf in
/-- The map `w ⊗ v ↦ q ^ deg w • w ⊗ N' v`, the twist of `E[W]` by `ω` tensored with `N'`,
commutes with the action of `W'` whose coinvariants form the tensor model. -/
theorem map_charTwist_comp_tprod (D' : WeilDeligneParameter E W' V' deg' (q ^ f)) (g : W') :
    TensorProduct.map (MonoidAlgebra.charTwist (omega deg hq)).toLinearMap D'.N ∘ₗ
        tprod ((leftRegular E W).comp ι) D'.r g =
      tprod ((leftRegular E W).comp ι) D'.r g ∘ₗ
        TensorProduct.map (MonoidAlgebra.charTwist (omega deg hq)).toLinearMap D'.N := by
  ext w v
  -- `q ^ deg (ι g) = (q ^ f) ^ deg' g` cancels the factor `((q ^ f) ^ deg' g)⁻¹` from `N'`.
  have hdeg : (q : E) ^ (deg (ι g)).toAdd = ((q : E) ^ f) ^ (deg' g).toAdd := by
    rw [hf, zpow_mul, zpow_natCast]
  simp [N_apply_r_apply, TensorProduct.smul_tmul', hdeg,
    inv_mul_cancel_left₀ (zpow_ne_zero _ (pow_ne_zero _ hq))]

/-- **The monodromy of the tensor model** `IndV ι r' = (E[W] ⊗ V')_{W'}`:
`⟦w ⊗ v⟧ ↦ q ^ deg w • ⟦w ⊗ N' v⟧`, the left-coset formula `g ⊗ v ↦ q ^ (-deg g) • g ⊗ N' v`
under `g = w⁻¹`. -/
def indVN (D' : WeilDeligneParameter E W' V' deg' (q ^ f)) : Module.End E (IndV ι D'.r) :=
  Coinvariants.map _ _
    ⟨TensorProduct.map (MonoidAlgebra.charTwist (omega deg hq)).toLinearMap D'.N,
      fun g ↦ map_charTwist_comp_tprod ι f hf hq D' g⟩

variable {ι f hf hq}

/-- The monodromy of the tensor model on a generator: `N ⟦w ⊗ v⟧ = q ^ deg w • ⟦w ⊗ N' v⟧`. -/
-- Not `@[simp]`, like Mathlib's `Representation.ind_mk`: `IndV.mk` is reducible, so `simp` unfolds
-- the left-hand side to `Coinvariants.mk` of a pure tensor (`simpNF`).
theorem indVN_mk (D' : WeilDeligneParameter E W' V' deg' (q ^ f)) (w : W) (v : V') :
    indVN ι f hf hq D' (IndV.mk ι D'.r w v) =
      (q : E) ^ (deg w).toAdd • IndV.mk ι D'.r w (D'.N v) := by
  simp [indVN, Coinvariants.map_mk, ← map_smul, TensorProduct.smul_tmul']

/-- `indVN_mk` as an identity of linear maps out of `V'`. -/
theorem indVN_comp_mk (D' : WeilDeligneParameter E W' V' deg' (q ^ f)) (w : W) :
    indVN ι f hf hq D' ∘ₗ IndV.mk ι D'.r w =
      (q : E) ^ (deg w).toAdd • (IndV.mk ι D'.r w ∘ₗ D'.N) :=
  LinearMap.ext fun v ↦ indVN_mk (hf := hf) (hq := hq) D' w v

/-- Powers of the tensor-model monodromy: `N ^ k ⟦w ⊗ v⟧ = (q ^ deg w) ^ k • ⟦w ⊗ N' ^ k v⟧`. -/
theorem indVN_pow_mk (D' : WeilDeligneParameter E W' V' deg' (q ^ f)) (k : ℕ) (w : W) (v : V') :
    (indVN ι f hf hq D' ^ k) (IndV.mk ι D'.r w v) =
      ((q : E) ^ (deg w).toAdd) ^ k • IndV.mk ι D'.r w ((D'.N ^ k) v) := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_apply_eq_comp, indVN_mk, map_smul, ih]
    simp [smul_smul, pow_succ, mul_apply_eq_comp, mul_comm]

/-- `indVN_pow_mk` as an identity of linear maps out of `V'`. -/
theorem indVN_pow_comp_mk (D' : WeilDeligneParameter E W' V' deg' (q ^ f)) (k : ℕ) (w : W) :
    (indVN ι f hf hq D' ^ k) ∘ₗ IndV.mk ι D'.r w =
      ((q : E) ^ (deg w).toAdd) ^ k • (IndV.mk ι D'.r w ∘ₗ D'.N ^ k) :=
  LinearMap.ext fun v ↦ indVN_pow_mk D' k w v

/-- The tensor-model monodromy is nilpotent. -/
theorem isNilpotent_indVN (D' : WeilDeligneParameter E W' V' deg' (q ^ f)) :
    IsNilpotent (indVN ι f hf hq D') := by
  obtain ⟨k, hk⟩ := D'.isNilpotent_N
  refine ⟨k, IndV.hom_ext _ _ fun w ↦ ?_⟩
  rw [indVN_pow_comp_mk, hk]
  simp

/-- The tensor-model monodromy satisfies the conjugation relation for `q` with respect to
Mathlib's induced representation `Representation.ind ι r'`. -/
theorem ind_mul_indVN_mul_ind_inv (D' : WeilDeligneParameter E W' V' deg' (q ^ f)) (x : W) :
    Representation.ind ι D'.r x * indVN ι f hf hq D' * Representation.ind ι D'.r x⁻¹ =
      (q : E) ^ (deg x).toAdd • indVN ι f hf hq D' := by
  refine IndV.hom_ext _ _ fun w ↦ LinearMap.ext fun v ↦ ?_
  -- Evaluate only the outer compositions: `simp` would also unfold the reducible `IndV.mk`.
  rw [LinearMap.comp_apply]
  conv_rhs => rw [LinearMap.comp_apply]
  simp only [mul_apply_eq_comp, ind_mk, inv_inv, indVN_mk, map_smul, mul_inv_cancel_right,
    LinearMap.smul_apply, smul_smul]
  -- The scalars: `q ^ deg (w x) = q ^ deg x * q ^ deg w`.
  congr 1
  rw [map_mul, toAdd_mul, zpow_add₀ hq]
  ring

section FiniteIndex

variable {S : Subgroup W} [TopologicalSpace S] [DecidableRel (QuotientGroup.rightRel S)]
  {degS : S →* Multiplicative ℤ} {hf : ∀ w : S, (deg (S.subtype w)).toAdd = f * (degS w).toAdd}

/-- **The comparison map intertwines the monodromies.** For a subgroup `S ≤ W`, Mathlib's map
`Rep.indToCoind` from the tensor model to the function model, an isomorphism when `S` has finite
index (`Rep.indCoindIso`), carries the tensor-model monodromy `indVN` to the function-model
monodromy `indN`. -/
theorem indToCoind_indVN (D' : WeilDeligneParameter E S V' degS (q ^ f))
    (x : IndV S.subtype D'.r) :
    (Rep.of D'.r).indToCoind (indVN S.subtype f hf hq D' x) =
      indN S.subtype f hf hq D' ((Rep.of D'.r).indToCoind x) := by
  suffices h : (Rep.of D'.r).indToCoind ∘ₗ indVN S.subtype f hf hq D' =
      indN S.subtype f hf hq D' ∘ₗ (Rep.of D'.r).indToCoind from LinearMap.congr_fun h x
  refine IndV.hom_ext _ _ fun h ↦ LinearMap.ext fun v ↦ Subtype.ext (funext fun w ↦ ?_)
  -- `TauCeti.indToCoind_mk`, stated for the generators `IndV.mk S.subtype D'.r h a`.
  have key (a : V') : ((Rep.of D'.r).indToCoind (IndV.mk S.subtype D'.r h a)).val =
      Rep.indToCoindAux (Rep.of D'.r) h a :=
    indToCoind_mk (A := Rep.of D'.r) h a
  -- Evaluate only the outer compositions: `simp` would also unfold the reducible `IndV.mk`.
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  conv_rhs => rw [LinearMap.comp_apply, LinearMap.comp_apply]
  rw [indVN_mk, map_smul, Submodule.coe_smul, Pi.smul_apply, indN_apply, key, key]
  by_cases hr : (QuotientGroup.rightRel S).r w h
  · obtain ⟨s, rfl⟩ : ∃ s : S, (s : W) * h = w := hr
    rw [Rep.indToCoindAux_mul_snd, Rep.indToCoindAux_mul_snd, Rep.indToCoindAux_self,
      Rep.indToCoindAux_self]
    simp only [N_apply_r_apply, smul_smul]
    rw [← Subgroup.subtype_apply, zpow_deg_map_mul_mul_zpow_neg S.subtype f hf hq s h]
  · simp [Rep.indToCoindAux_of_not_rel _ _ _ hr]

end FiniteIndex

end WeilDeligneParameter

end TauCeti
