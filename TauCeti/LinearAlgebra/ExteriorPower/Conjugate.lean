/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Complex.Conjugate
public import TauCeti.LinearAlgebra.ExteriorPower.Basic

/-!
# Exterior powers of conjugate complex modules

Conjugation commutes with every exterior power. The comparison is complex-linear:
conjugating each vector and conjugating its wedge conjugates a scalar twice.
The construction uses the universal alternating map, with no basis, finite-dimensionality,
norm or topology. In particular it includes the zeroth exterior power.
-/

public section

noncomputable section

open TauCeti TauCeti.Conjugate

namespace exteriorPower

universe u v

variable {V : Type u} {W : Type v} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

/-- Conjugate the entries of an alternating tuple and then conjugate its exterior product. -/
private def conjugateAlternating (n : ℕ) :
    Conjugate V [⋀^Fin n]→ₗ[ℂ] Conjugate (⋀[ℂ]^n V) where
  __ := (toConjₗ : (⋀[ℂ]^n V) ≃ₗ⋆[ℂ] Conjugate (⋀[ℂ]^n V)).toLinearMap.compMultilinearMap
    ((ιMulti ℂ n).toMultilinearMap.compLinearMap
      fun _ => (toConjₗ : V ≃ₗ⋆[ℂ] Conjugate V).symm.toLinearMap)
  map_eq_zero_of_eq' a i j hij hne := by
    simpa only [MultilinearMap.toFun_eq_coe, LinearMap.compMultilinearMap_apply,
      MultilinearMap.compLinearMap_apply,
      LinearEquiv.coe_coe, coe_toConjₗ, coe_toConjₗ_symm, toConj_zero,
      AlternatingMap.coe_multilinearMap] using
      congrArg (toConj : (⋀[ℂ]^n V) ≃ Conjugate (⋀[ℂ]^n V))
        ((ιMulti ℂ n (M := V)).map_eq_zero_of_eq (fun k => ofConj (a k))
          (congrArg (ofConj : Conjugate V ≃ V) hij) hne)

/-- The canonical map from an exterior power of a conjugate to the conjugate exterior power. -/
def conjugateMap (n : ℕ) : ⋀[ℂ]^n (Conjugate V) →ₗ[ℂ] Conjugate (⋀[ℂ]^n V) :=
  alternatingMapLinearEquiv (conjugateAlternating n)

@[simp] theorem conjugateMap_ιMulti (n : ℕ) (a : Fin n → Conjugate V) :
    conjugateMap n (ιMulti ℂ n a) = toConj (ιMulti ℂ n (ofConj ∘ a)) := by
  rw [conjugateMap, alternatingMapLinearEquiv_apply_ιMulti]
  simp only [conjugateAlternating, AlternatingMap.coe_mk,
    LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
    LinearEquiv.coe_coe, coe_toConjₗ, coe_toConjₗ_symm, Function.comp_def,
    AlternatingMap.coe_multilinearMap]

/-- The inverse map is obtained by applying the same construction to the conjugate module
and cancelling the two conjugations. -/
private def conjugateMapInv (n : ℕ) :
    Conjugate (⋀[ℂ]^n V) →ₗ[ℂ] ⋀[ℂ]^n (Conjugate V) :=
  doubleConjugateLinearEquiv.toLinearMap.comp
    (((conjugateMap n (V := Conjugate V)).comp (map n
      (doubleConjugateLinearEquiv : Conjugate (Conjugate V) ≃ₗ[ℂ] V).symm.toLinearMap)).conjugate)

private theorem conjugateMapInv_ιMulti (n : ℕ) (a : Fin n → V) :
    conjugateMapInv n (toConj (ιMulti ℂ n a)) = ιMulti ℂ n (toConj ∘ a) := by
  simp [conjugateMapInv, map_apply_ιMulti, Function.comp_def]

/-- Linear maps out of a conjugated exterior power agree when they agree on universal wedges. -/
@[ext] theorem conjugate_linearMap_ext {n : ℕ}
    {f g : Conjugate (⋀[ℂ]^n V) →ₗ[ℂ] W}
    (h : ∀ a : Fin n → V, f (toConj (ιMulti ℂ n a)) = g (toConj (ιMulti ℂ n a))) : f = g := by
  have h' : f.conjugate.comp doubleConjugateLinearEquiv.symm.toLinearMap =
      g.conjugate.comp doubleConjugateLinearEquiv.symm.toLinearMap := by
    apply linearMap_ext
    ext a
    simpa using congrArg toConj (h a)
  ext a
  simpa only [LinearMap.comp_apply, LinearMap.conjugate_apply, LinearEquiv.coe_coe,
    doubleConjugateLinearEquiv_symm_apply, ofConj_toConj, toConj_ofConj] using
    congrArg (fun k => ofConj (k (ofConj a))) h'

private theorem conjugateMapInv_comp (n : ℕ) :
    (conjugateMapInv n (V := V)).comp (conjugateMap n) = LinearMap.id := by
  apply linearMap_ext
  ext a
  simp [conjugateMapInv_ιMulti, Function.comp_def]

private theorem conjugateMap_comp_inv (n : ℕ) :
    (conjugateMap n (V := V)).comp (conjugateMapInv n) = LinearMap.id := by
  apply conjugate_linearMap_ext
  intro a
  simp [conjugateMapInv_ιMulti, Function.comp_def]

/-- Exterior powers commute with conjugation, at every degree and for arbitrary complex modules. -/
def conjugateEquiv (n : ℕ) : ⋀[ℂ]^n (Conjugate V) ≃ₗ[ℂ] Conjugate (⋀[ℂ]^n V) where
  __ := conjugateMap n
  invFun := conjugateMapInv n
  left_inv a := congrArg (fun f => f a) (conjugateMapInv_comp n)
  right_inv a := congrArg (fun f => f a) (conjugateMap_comp_inv n)

@[simp] theorem conjugateEquiv_toLinearMap (n : ℕ) :
    (conjugateEquiv n (V := V)).toLinearMap = conjugateMap n := by rfl

@[simp] theorem conjugateEquiv_ιMulti (n : ℕ) (a : Fin n → Conjugate V) :
    conjugateEquiv n (ιMulti ℂ n a) = toConj (ιMulti ℂ n (ofConj ∘ a)) :=
  conjugateMap_ιMulti n a

@[simp] theorem conjugateEquiv_symm_ιMulti (n : ℕ) (a : Fin n → V) :
    (conjugateEquiv n).symm (toConj (ιMulti ℂ n a)) = ιMulti ℂ n (toConj ∘ a) :=
  conjugateMapInv_ιMulti n a

/-- The canonical comparison commutes with every linear map, including maps between
modules in independent universes. -/
theorem conjugateMap_naturality (n : ℕ) (f : V →ₗ[ℂ] W) :
    (conjugateMap n).comp (map n f.conjugate) =
      (map n f).conjugate.comp (conjugateMap n) := by
  apply linearMap_ext
  ext a
  simp [map_apply_ιMulti, Function.comp_def]

/-- The naturality square evaluated on an arbitrary exterior-power vector. -/
theorem conjugateEquiv_naturality (n : ℕ) (f : V →ₗ[ℂ] W)
    (a : ⋀[ℂ]^n (Conjugate V)) :
    conjugateEquiv n (map n f.conjugate a) =
      (map n f).conjugate (conjugateEquiv n a) := by
  exact LinearMap.congr_fun (conjugateMap_naturality n f) a

/-- Applying the exterior comparison twice agrees with the canonical double-conjugation
identification of the original module. -/
theorem conjugateEquiv_double (n : ℕ) :
    doubleConjugateLinearEquiv.toLinearMap.comp
      ((conjugateEquiv n (V := V)).conjugate.toLinearMap.comp
        (conjugateEquiv n (V := Conjugate V)).toLinearMap) =
      map n (doubleConjugateLinearEquiv : Conjugate (Conjugate V) ≃ₗ[ℂ] V).toLinearMap := by
  apply linearMap_ext
  ext a
  simp [Function.comp_def]

/-- Naturality after identifying two exterior degrees. -/
theorem conjugateEquiv_ofEq_map {U : Type*} {V : Type*}
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    {n m : ℕ} (h : n = m) (f : U →ₗ[ℂ] V) (a : ⋀[ℂ]^n (Conjugate U)) :
    conjugateEquiv m
      (LinearEquiv.ofEq _ _ (congrArg (fun k => ⋀[ℂ]^k (Conjugate V)) h)
        (map n f.conjugate a)) =
      (map m f).conjugate
        (conjugateEquiv m
          (LinearEquiv.ofEq _ _ (congrArg (fun k => ⋀[ℂ]^k (Conjugate U)) h) a)) := by
  cases h
  exact conjugateEquiv_naturality n f a

/-- The full conjugation square also commutes with changes of exterior degree along equalities.
This keeps independent model-rank presentations explicit in native determinant comparisons. -/
theorem conjugateEquiv_ofEq_naturality {n n' m m' : ℕ}
    (hn : n = n') (hm : m = m') (h : n' = m') (hc : n = m)
    (f : V →ₗ[ℂ] W) (a : ⋀[ℂ]^n (Conjugate V)) :
    conjugateEquiv m'
      (LinearEquiv.ofEq _ _ (congrArg (fun k => ⋀[ℂ]^k (Conjugate W)) hm)
        (LinearEquiv.ofEq _ _ (congrArg (fun k => ⋀[ℂ]^k (Conjugate W)) hc)
          (map n f.conjugate a))) =
    toConj (LinearEquiv.ofEq _ _ (congrArg (fun k => ⋀[ℂ]^k W) h)
      (map n' f (ofConj (conjugateEquiv n'
        (LinearEquiv.ofEq _ _ (congrArg (fun k => ⋀[ℂ]^k (Conjugate V)) hn) a))))) := by
  cases hn
  cases hm
  cases h
  simpa only [LinearEquiv.ofEq_rfl, LinearEquiv.refl_apply, LinearMap.conjugate_apply] using
    conjugateEquiv_naturality n f a

/-- Double conjugation commutes with the rank transports of independent model presentations. -/
theorem conjugateEquiv_ofEq_double {n m k : ℕ} (h : n = m) (h' : m = k)
    (a : ⋀[ℂ]^n (Conjugate (Conjugate V))) :
    ofConj (conjugateEquiv k
      (LinearEquiv.ofEq _ _ (congrArg (fun j => ⋀[ℂ]^j (Conjugate V)) h')
        (ofConj (conjugateEquiv m
          (LinearEquiv.ofEq _ _ (congrArg (fun j => ⋀[ℂ]^j (Conjugate (Conjugate V))) h)
            a))))) =
    LinearEquiv.ofEq _ _ (congrArg (fun j => ⋀[ℂ]^j V) (h.trans h'))
      (map n (doubleConjugateLinearEquiv : Conjugate (Conjugate V) ≃ₗ[ℂ] V).toLinearMap a) := by
  cases h
  cases h'
  have hd := congrArg (fun g => g a) (conjugateEquiv_double n (V := V))
  simpa only [LinearEquiv.ofEq_rfl, LinearEquiv.refl_apply, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, LinearEquiv.conjugate_apply,
    doubleConjugateLinearEquiv_apply, ofConj_toConj] using hd

end exteriorPower
