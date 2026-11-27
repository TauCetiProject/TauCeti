/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.FiniteIndex
public import Mathlib.RepresentationTheory.Induced
public import TauCeti.RepresentationTheory.WeilDeligne.Induction

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
`N ⟦w ⊗ v⟧ = q ^ deg w • ⟦w ⊗ N' v⟧` (`TauCeti.WeilDeligneParameter.indVN_mk`). It is
well defined on the coinvariants because `N' (r' g v) = (q ^ f) ^ (-deg' g) • r' g (N' v)` and
`deg (ι g) = f · deg' g`. It is nilpotent and satisfies the conjugation relation for `q` with
respect to `Representation.ind ι r'`.

For a subgroup `S ≤ W` of finite index, Mathlib's isomorphism `Rep.indToCoind` between the two
models intertwines this monodromy with the function-model monodromy
`TauCeti.WeilDeligneParameter.indN` (`TauCeti.WeilDeligneParameter.indToCoind_comp_indVN`), so
the two inductions agree as parameters.

## Main definitions

* `TauCeti.WeilDeligneParameter.indVN`: the monodromy `⟦w ⊗ v⟧ ↦ q ^ deg w • ⟦w ⊗ N' v⟧` on the
  tensor model.

## Main results

* `TauCeti.WeilDeligneParameter.isNilpotent_indVN` and
  `TauCeti.WeilDeligneParameter.ind_mul_indVN_mul_ind_inv`: it is nilpotent and satisfies the
  conjugation relation for `q`.
* `TauCeti.WeilDeligneParameter.indToCoind_comp_indVN`: Mathlib's comparison map from the tensor
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

section Weight

variable (deg) (hq : (q : E) ≠ 0)

/-- The character `w ↦ q ^ deg w • w` of `W` into its group algebra. -/
def weightHom : W →* E[W] where
  toFun w := (q : E) ^ (deg w).toAdd • MonoidAlgebra.single w 1
  map_one' := by simp [MonoidAlgebra.one_def]
  map_mul' w w' := by
    rw [map_mul, toAdd_mul, zpow_add₀ hq, smul_mul_smul_comm, MonoidAlgebra.single_mul_single,
      one_mul]

/-- The `E`-algebra endomorphism of `E[W]` scaling `w` by `q ^ deg w`. -/
def weight : E[W] →ₐ[E] E[W] :=
  MonoidAlgebra.lift E E[W] W (weightHom deg hq)

@[simp]
theorem weight_single (w : W) (c : E) :
    weight deg hq (MonoidAlgebra.single w c) =
      MonoidAlgebra.single w (((q : E) ^ (deg w).toAdd) * c) := by
  simp [weight, weightHom, mul_comm]

end Weight

variable (ι : W' →* W) (f : ℕ) (hf : ∀ w, (deg (ι w)).toAdd = f * (deg' w).toAdd)
  (hq : (q : E) ≠ 0)

include hf in
/-- The weighted tensor map `w ⊗ v ↦ q ^ deg w • w ⊗ N' v` commutes with the action of `W'`
whose coinvariants form the tensor model. -/
theorem weight_map_comm (D' : WeilDeligneParameter E W' V' deg' (q ^ f)) (g : W') :
    TensorProduct.map (weight deg hq).toLinearMap D'.N ∘ₗ
        tprod ((leftRegular E W).comp ι) D'.r g =
      tprod ((leftRegular E W).comp ι) D'.r g ∘ₗ
        TensorProduct.map (weight deg hq).toLinearMap D'.N := by
  ext w v
  -- The exponent identity `deg (ι g) + deg w - f deg' g = deg w`.
  have hexp : (((q : E) ^ f) ^ (deg' g).toAdd)⁻¹ *
      (q : E) ^ ((deg (ι g)).toAdd + (deg w).toAdd) = (q : E) ^ (deg w).toAdd := by
    rw [hf, zpow_add₀ hq, ← zpow_natCast, ← zpow_mul, inv_mul_cancel_left₀ (zpow_ne_zero _ hq)]
  simp [N_apply_r_apply, TensorProduct.smul_tmul', hexp]

/-- **The monodromy of the tensor model** `IndV ι r' = (E[W] ⊗ V')_{W'}`:
`⟦w ⊗ v⟧ ↦ q ^ deg w • ⟦w ⊗ N' v⟧`, the left-coset formula `g ⊗ v ↦ q ^ (-deg g) • g ⊗ N' v`
under `g = w⁻¹`. -/
def indVN (D' : WeilDeligneParameter E W' V' deg' (q ^ f)) : Module.End E (IndV ι D'.r) :=
  Coinvariants.map _ _
    ⟨TensorProduct.map (weight deg hq).toLinearMap D'.N, fun g ↦ weight_map_comm ι f hf hq D' g⟩

variable {ι f hf hq}

/-- The monodromy of the tensor model on a generator: `N ⟦w ⊗ v⟧ = q ^ deg w • ⟦w ⊗ N' v⟧`. -/
theorem indVN_mk (D' : WeilDeligneParameter E W' V' deg' (q ^ f)) (w : W) (v : V') :
    indVN ι f hf hq D' (IndV.mk ι D'.r w v) =
      (q : E) ^ (deg w).toAdd • IndV.mk ι D'.r w (D'.N v) := by
  simp [indVN, Coinvariants.map_mk, ← map_smul, TensorProduct.smul_tmul']

/-- `indVN_mk` as an identity of linear maps out of `V'`. -/
theorem indVN_comp_mk (D' : WeilDeligneParameter E W' V' deg' (q ^ f)) (w : W) :
    indVN ι f hf hq D' ∘ₗ IndV.mk ι D'.r w =
      (q : E) ^ (deg w).toAdd • (IndV.mk ι D'.r w ∘ₗ D'.N) :=
  LinearMap.ext fun v ↦ indVN_mk (hf := hf) (hq := hq) D' w v

/-- `indVN_pow_mk` as an identity of linear maps out of `V'`. -/
theorem indVN_pow_comp_mk (D' : WeilDeligneParameter E W' V' deg' (q ^ f)) (k : ℕ) (w : W) :
    (indVN ι f hf hq D' ^ k) ∘ₗ IndV.mk ι D'.r w =
      ((q : E) ^ (deg w).toAdd) ^ k • (IndV.mk ι D'.r w ∘ₗ D'.N ^ k) := by
  induction k with
  | zero => rw [pow_zero, pow_zero, one_smul]; rfl
  | succ k ih =>
    rw [pow_succ, Module.End.mul_eq_comp, LinearMap.comp_assoc, indVN_comp_mk,
      LinearMap.comp_smul, ← LinearMap.comp_assoc, ih, LinearMap.smul_comp, smul_smul,
      ← pow_succ', LinearMap.comp_assoc, ← Module.End.mul_eq_comp, ← pow_succ]

/-- Powers of the tensor-model monodromy: `N ^ k ⟦w ⊗ v⟧ = (q ^ deg w) ^ k • ⟦w ⊗ N' ^ k v⟧`. -/
theorem indVN_pow_mk (D' : WeilDeligneParameter E W' V' deg' (q ^ f)) (k : ℕ) (w : W) (v : V') :
    (indVN ι f hf hq D' ^ k) (IndV.mk ι D'.r w v) =
      ((q : E) ^ (deg w).toAdd) ^ k • IndV.mk ι D'.r w ((D'.N ^ k) v) :=
  LinearMap.congr_fun (indVN_pow_comp_mk D' k w) v

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
  refine IndV.hom_ext _ _ fun w ↦ ?_
  have hmk (h w : W) : Representation.ind ι D'.r h ∘ₗ IndV.mk ι D'.r w =
      IndV.mk ι D'.r (w * h⁻¹) :=
    LinearMap.ext fun v ↦ ind_mk ι D'.r h w v
  rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, LinearMap.comp_assoc, hmk, inv_inv,
    LinearMap.comp_assoc, indVN_comp_mk, LinearMap.comp_smul, ← LinearMap.comp_assoc, hmk,
    mul_inv_cancel_right, LinearMap.smul_comp, indVN_comp_mk, smul_smul, map_mul, toAdd_mul,
    zpow_add₀ hq, mul_comm]

section FiniteIndex

variable {S : Subgroup W} [TopologicalSpace S] [DecidableRel (QuotientGroup.rightRel S)]
  {degS : S →* Multiplicative ℤ} {hf : ∀ w : S, (deg (S.subtype w)).toAdd = f * (degS w).toAdd}

/-- **The tensor and function models of induction agree.** For a subgroup `S ≤ W`, Mathlib's map
`Rep.indToCoind` from the tensor model to the function model, an isomorphism when `S` has finite
index (`Rep.indCoindIso`), carries the tensor-model monodromy `indVN` to the function-model
monodromy `indN`. -/
theorem indToCoind_indVN (D' : WeilDeligneParameter E S V' degS (q ^ f))
    (x : IndV S.subtype D'.r) :
    (Rep.of D'.r).indToCoind (indVN S.subtype f hf hq D' x) =
      indN S.subtype f hf hq D' ((Rep.of D'.r).indToCoind x) := by
  suffices h : (Rep.of D'.r).indToCoind ∘ₗ indVN S.subtype f hf hq D' =
      indN S.subtype f hf hq D' ∘ₗ (Rep.of D'.r).indToCoind from LinearMap.congr_fun h x
  have key (h : W) (v : V') : (((Rep.of D'.r).indToCoind (IndV.mk S.subtype D'.r h v) :
      coindV S.subtype D'.r) : W → V') = Rep.indToCoindAux (Rep.of D'.r) h v := by
    simp
    rfl
  refine IndV.hom_ext _ _ fun h ↦ ?_
  rw [LinearMap.comp_assoc, indVN_comp_mk, LinearMap.comp_smul, ← LinearMap.comp_assoc]
  refine LinearMap.ext fun v ↦ Subtype.ext (funext fun w ↦ ?_)
  change (q : E) ^ (deg h).toAdd • ((Rep.of D'.r).indToCoind
      (IndV.mk S.subtype D'.r h (D'.N v)) : W → V') w =
    ((indN S.subtype f hf hq D' ((Rep.of D'.r).indToCoind (IndV.mk S.subtype D'.r h v)) :
      coindV S.subtype D'.r) : W → V') w
  rw [indN_apply, key, key]
  rcases em ((QuotientGroup.rightRel S).r w h) with ⟨s, rfl⟩ | hn
  · -- The exponent identity `deg (s h) - f deg' s = deg h`.
    have hs : (deg (s : W)).toAdd = f * (degS s).toAdd := hf s
    have hexp : (q : E) ^ (deg ((s : W) * h)).toAdd * ((q ^ f : ℕ) : E) ^ (-(degS s).toAdd) =
        (q : E) ^ (deg h).toAdd := by
      rw [map_mul, toAdd_mul, hs, zpow_add₀ hq, mul_right_comm, Nat.cast_pow, ← zpow_natCast,
        ← zpow_mul, ← zpow_add₀ hq, mul_neg, add_neg_cancel, zpow_zero, one_mul]
    beta_reduce
    rw [Subgroup.smul_def, smul_eq_mul, Rep.indToCoindAux_mul_snd, Rep.indToCoindAux_mul_snd,
      Rep.indToCoindAux_self, Rep.indToCoindAux_self, Rep.of_ρ, N_apply_r_apply, smul_smul, hexp]
  · rw [Rep.indToCoindAux_of_not_rel _ _ _ hn, Rep.indToCoindAux_of_not_rel _ _ _ hn, map_zero,
      smul_zero, smul_zero]

end FiniteIndex

end WeilDeligneParameter

end TauCeti
