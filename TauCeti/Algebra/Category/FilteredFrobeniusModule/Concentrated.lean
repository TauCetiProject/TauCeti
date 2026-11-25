/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FilteredFrobeniusModule.Twist

/-!
# Filtered Frobenius modules with a single filtration jump

A `W`-module `V` with a `σ`-semilinear endomorphism `ψ` gives, for each integer `j`, a filtered
Frobenius module `concentrated ϖ ψ j` with a single filtration jump in degree `j`:
`Fil^i = V` for `i ≤ j` and `Fil^i = 0` for `i > j`, with `φ^j = ψ`, hence
`φ^i = ϖ ^ (j - i) • ψ` for `i ≤ j`, and `φ^i = 0` for `i > j`. These are the objects of
Fontaine–Laffaille's categories with weights in `[j, j]`; for instance `W(k) / p` with `ψ` the
Frobenius and `j = 0` is the unit object of `MF_tor^[0,0]`, and the module `W` with `ψ = σ` is
the free rank-one object of jump `j`.

Such an object is supported in `[a, b]` iff `a ≤ j ≤ b` (when `V ≠ 0`), and it is generating iff
the image of `ψ` spans `V`. So the zero semilinear map on a nonzero module gives a filtered
Frobenius module which is not generating. The morphisms between two such objects with the same
jump are the linear maps intertwining the semilinear endomorphisms, and twisting by `k` moves the
jump from `j` to `j + k`.

## Main definitions

* `TauCeti.FilteredFrobeniusModule.concentrated ϖ ψ j`: the filtered Frobenius module with a
  single jump in degree `j` and `φ^j = ψ`.
* `TauCeti.FilteredFrobeniusModule.concentratedHomEquiv`: morphisms between two such objects
  with the same jump are the intertwining linear maps.
* `TauCeti.FilteredFrobeniusModule.concentratedTwistIso`: the twist by `k` moves the jump to
  `j + k`.

## Main results

* `TauCeti.FilteredFrobeniusModule.isSupportedIn_concentrated_iff`: the support of a nonzero
  object with jump `j` is any interval containing `j`.
* `TauCeti.FilteredFrobeniusModule.isGenerating_concentrated_iff`: generation is equivalent to
  the image of `ψ` spanning `V`.
* `TauCeti.FilteredFrobeniusModule.isGenerating_concentrated_toSemilinearMap`: the free rank-one
  object `W` with `φ^j = σ` is generating.

## References

* J.-M. Fontaine and G. Laffaille, *Construction de représentations p-adiques*, Ann. Sci. École
  Norm. Sup. (4) 15 (1982), §§1.2 and 4.
-/

public section

open CategoryTheory

universe v u

namespace TauCeti.FilteredFrobeniusModule

variable {W : Type u} [CommRing W] {σ : W →+* W} (ϖ : W)
variable {V V' : Type v} [AddCommGroup V] [Module W V] [AddCommGroup V'] [Module W V']

/-- The filtered Frobenius module on `V` with a single filtration jump in degree `j`:
`Fil^i = V` for `i ≤ j` and `Fil^i = 0` for `i > j`, with `φ^i = ϖ ^ (j - i) • ψ` for `i ≤ j`
and `φ^i = 0` for `i > j`. -/
abbrev concentrated (ψ : V →ₛₗ[σ] V) (j : ℤ) : FilteredFrobeniusModule.{v} σ ϖ where
  toModuleCat := ModuleCat.of W V
  fil i := if i ≤ j then ⊤ else ⊥
  fil_antitone a b hab := by
    dsimp only
    split_ifs <;> first | exact le_rfl | exact le_top | omega
  iSup_fil := top_le_iff.1 (le_iSup_of_le j (by simp))
  iInf_fil := le_bot_iff.1 (iInf_le_of_le (j + 1) (by simp))
  phi i := if i ≤ j then ϖ ^ (j - i).toNat • ψ.comp (Submodule.subtype _) else 0
  phi_succ i x hx := by
    by_cases h : i + 1 ≤ j
    · simp only [show i ≤ j by omega, h, ↓reduceIte, LinearMap.smul_apply,
        LinearMap.comp_apply, Submodule.subtype_apply, ← mul_smul, ← pow_succ']
      congr 2
      omega
    · have hx0 : x = 0 := by simpa [h] using hx
      subst hx0
      exact (map_zero _).trans ((smul_zero ϖ).symm.trans (congrArg (ϖ • ·) (map_zero _).symm))

variable {ϖ} (ψ : V →ₛₗ[σ] V) (ψ' : V' →ₛₗ[σ] V') (j : ℤ)

/-- An element lies in `Fil^i` of the object with a single jump `j` iff `i ≤ j` or it is zero. -/
theorem mem_concentrated_fil_iff {i : ℤ} {x : V} :
    x ∈ (concentrated ϖ ψ j).fil i ↔ i ≤ j ∨ x = 0 := by
  by_cases h : i ≤ j <;> simp [h]

theorem concentrated_fil_of_le {i : ℤ} (h : i ≤ j) : (concentrated ϖ ψ j).fil i = ⊤ := by
  simp [h]

theorem concentrated_fil_of_lt {i : ℤ} (h : j < i) : (concentrated ϖ ψ j).fil i = ⊥ := by
  simp [not_le.2 h]

theorem concentrated_phi_of_le {i : ℤ} (h : i ≤ j) (x : V) (hx) :
    (concentrated ϖ ψ j).phi i ⟨x, hx⟩ = ϖ ^ (j - i).toNat • ψ x := by
  simp [h]

theorem concentrated_phi_self (x : V) (hx) : (concentrated ϖ ψ j).phi j ⟨x, hx⟩ = ψ x := by
  simp

theorem concentrated_phi_of_lt {i : ℤ} (h : j < i) (x : V) (hx) :
    (concentrated ϖ ψ j).phi i ⟨x, hx⟩ = 0 := by
  simp [not_le.2 h]

/-- An object with a single jump `j` is supported in every interval containing `j`. -/
theorem isSupportedIn_concentrated {a b : ℤ} (ha : a ≤ j) (hb : j ≤ b) :
    (concentrated ϖ ψ j).IsSupportedIn a b :=
  (isSupportedIn_iff _ a b).2
    ⟨concentrated_fil_of_le ψ j ha, concentrated_fil_of_lt ψ j (by omega)⟩

/-- A nonzero object with a single jump `j` is supported in `[a, b]` iff `a ≤ j ≤ b`. -/
theorem isSupportedIn_concentrated_iff [Nontrivial V] {a b : ℤ} :
    (concentrated ϖ ψ j).IsSupportedIn a b ↔ a ≤ j ∧ j ≤ b := by
  rw [isSupportedIn_iff]
  refine ⟨fun ⟨ha, hb⟩ => ⟨?_, ?_⟩, fun h => (isSupportedIn_iff _ a b).1
    (isSupportedIn_concentrated ψ j h.1 h.2)⟩
  · by_contra h
    rw [concentrated_fil_of_lt ψ j (not_le.1 h)] at ha
    exact bot_ne_top ha
  · by_contra h
    rw [concentrated_fil_of_le ψ j (by omega)] at hb
    exact top_ne_bot hb

/-- The range of the divided Frobenius map in degree `j` is the range of `ψ`. -/
theorem range_concentrated_phi_self :
    Set.range ((concentrated ϖ ψ j).phi j) = Set.range ψ := by
  ext y
  refine ⟨fun ⟨⟨x, hx⟩, hy⟩ => ⟨x, by simpa using hy⟩, fun ⟨x, hy⟩ => ?_⟩
  exact ⟨⟨x, by simp⟩, by simpa using hy⟩

/-- An object with a single jump is generating iff the image of `ψ` spans `V`. -/
@[simp]
theorem isGenerating_concentrated_iff :
    (concentrated ϖ ψ j).IsGenerating ↔ Submodule.span W (Set.range ψ) = ⊤ := by
  rw [isGenerating_iff_of_isSupportedIn (isSupportedIn_concentrated ψ j le_rfl le_rfl),
    Set.Icc_self, iSup_singleton, range_concentrated_phi_self]

/-- The zero semilinear map on a nonzero module gives a filtered Frobenius module that is not
generating. -/
theorem not_isGenerating_concentrated_zero [Nontrivial V] :
    ¬ (concentrated ϖ (0 : V →ₛₗ[σ] V) j).IsGenerating := by
  have h0 : Set.range (0 : V →ₛₗ[σ] V) = {0} := by
    ext
    simp [eq_comm]
  rw [isGenerating_concentrated_iff, h0, Submodule.span_zero_singleton]
  exact bot_ne_top

/-- The free rank-one object `W` with `φ^j = σ` is generating, since `σ 1 = 1`. -/
theorem isGenerating_concentrated_toSemilinearMap :
    (concentrated ϖ σ.toSemilinearMap j).IsGenerating := by
  rw [isGenerating_concentrated_iff, eq_top_iff, ← Ideal.span_singleton_one]
  exact Submodule.span_mono (Set.singleton_subset_iff.2 ⟨1, map_one σ⟩)

/-- A linear map intertwining two semilinear endomorphisms is a morphism between the objects
with the same single jump. -/
def concentratedHom (f : V →ₗ[W] V') (hf : ∀ x, f (ψ x) = ψ' (f x)) :
    concentrated ϖ ψ j ⟶ concentrated ϖ ψ' j where
  hom := f
  map_fil _ _ hx := (mem_concentrated_fil_iff (ϖ := ϖ) ψ' j).2
    (((mem_concentrated_fil_iff (ϖ := ϖ) ψ j).1 hx).imp_right fun h => by rw [h, map_zero])
  hom_phi i x hx := by
    by_cases h : i ≤ j
    · simp [h, hf]
    · simp [h]

@[simp]
theorem concentratedHom_hom (f : V →ₗ[W] V') (hf : ∀ x, f (ψ x) = ψ' (f x)) :
    (concentratedHom (ϖ := ϖ) ψ ψ' j f hf).hom = f := (rfl)

/-- A morphism between objects with the same single jump `j` intertwines the semilinear
endomorphisms. -/
theorem Hom.hom_apply_concentrated (f : concentrated ϖ ψ j ⟶ concentrated ϖ ψ' j) (x : V) :
    f.hom (ψ x) = ψ' (f.hom x) := by
  simpa using f.hom_phi j x (by simp)

/-- Morphisms between objects with the same single jump `j` are the linear maps intertwining the
semilinear endomorphisms. -/
def concentratedHomEquiv :
    (concentrated ϖ ψ j ⟶ concentrated ϖ ψ' j) ≃
      {f : V →ₗ[W] V' // ∀ x, f (ψ x) = ψ' (f x)} where
  toFun f := ⟨f.hom, f.hom_apply_concentrated ψ ψ' j⟩
  invFun f := concentratedHom ψ ψ' j f.val f.property
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem concentratedHomEquiv_apply_coe (f : concentrated ϖ ψ j ⟶ concentrated ϖ ψ' j) :
    (concentratedHomEquiv ψ ψ' j f : V →ₗ[W] V') = f.hom := (rfl)

@[simp]
theorem concentratedHomEquiv_symm_apply_hom (f : {f : V →ₗ[W] V' // ∀ x, f (ψ x) = ψ' (f x)}) :
    ((concentratedHomEquiv (ϖ := ϖ) ψ ψ' j).symm f).hom = f.val := (rfl)

/-- Twisting an object with a single jump `j` by `k` gives the object with the single jump
`j + k`. -/
def concentratedTwistIso (k : ℤ) :
    (concentrated ϖ ψ j).twist k ≅ concentrated ϖ ψ (j + k) :=
  isoMk (LinearEquiv.refl W V) (fun i => by simp) fun i x hx => by
    by_cases h : i - k ≤ j
    · simp [h, show i ≤ j + k by omega, show j - (i - k) = j + k - i by ring]
    · simp [h, show ¬ i ≤ j + k by omega]

@[simp]
theorem concentratedTwistIso_hom_hom (k : ℤ) :
    (concentratedTwistIso (ϖ := ϖ) ψ j k).hom.hom = LinearMap.id := isoMk_hom_hom _ _ _

@[simp]
theorem concentratedTwistIso_inv_hom (k : ℤ) :
    (concentratedTwistIso (ϖ := ϖ) ψ j k).inv.hom = LinearMap.id := isoMk_inv_hom _ _ _

end TauCeti.FilteredFrobeniusModule
