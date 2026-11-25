/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import TauCeti.LinearAlgebra.LinearIndependent.Semilinear

/-!
# The centralizer of a semilinear map

Let `σ` be an endomorphism of a commutative semiring `E` fixing the image of `F`, and let
`φ : V → V` be `σ`-semilinear. The `E`-linear endomorphisms of `V` commuting with `φ` form an
`F`-subalgebra `semilinearCentralizer F σ hσ φ` of `Module.End E V`. It is not an `E`-submodule
in general: for `φ = σ` on `V = E`, multiplication by `a ∈ E` lies in it only when `σ a = a`.

For a Frobenius `φ` on the crystalline cohomology of a variety over a `p`-adic field, the unit
group of this centralizer is the group of automorphisms of the underlying `φ`-module. Hodge
filtrations giving isomorphic filtered `φ`-modules form one orbit of this group, so its dimension
bounds the dimension of that orbit. The main result is the dimension bound of Lawrence and
Venkatesh: if every element of `E` fixed by `σ` comes from the field `F` and `φ` is surjective,
then `dim_F Z(φ) ≤ (dim_E V)²` (`finrank_semilinearCentralizer_le`). The bound needs neither
finiteness of `E` over `F` nor finiteness of the order of `σ`. Its proof shows that elements of
`Z(φ)` that are linearly independent over `F` stay linearly independent over `E` in
`Module.End E V` (`linearIndependent_of_semilinearCentralizer`).

For a finite isocrystal `D`, `TauCeti.FiniteIsocrystal.mem_range_endRingHom` describes the same
endomorphisms as the image of the endomorphism ring of `D`.

## Main definitions

* `TauCeti.semilinearCentralizer F σ hσ φ`: the `F`-subalgebra of `Module.End E V` of
  endomorphisms commuting with the `σ`-semilinear map `φ`.

## Main results

* `TauCeti.semilinearCentralizer_id`: for `σ = id` it is the centralizer of `φ`.
* `TauCeti.mulLeft_mem_semilinearCentralizer_iff`: for `φ = σ` on `E`, multiplication by `a`
  lies in `Z(σ)` exactly when `σ a = a`.
* `TauCeti.map_conjAlgEquiv_semilinearCentralizer`: conjugating by a linear equivalence `u`
  identifies `Z(φ)` with `Z(u φ u⁻¹)`.
* `TauCeti.linearIndependent_of_semilinearCentralizer`: linear independence over `F` in `Z(φ)`
  implies linear independence over `E`.
* `TauCeti.finrank_semilinearCentralizer_le`: `dim_F Z(φ) ≤ (dim_E V)²`, with its rank form
  `TauCeti.rank_semilinearCentralizer_le` and the resulting finite-dimensionality
  `TauCeti.finiteDimensional_semilinearCentralizer`.

## References

* B. Lawrence and A. Venkatesh, *Diophantine problems and p-adic period mappings*,
  Invent. Math. 221 (2020), §2.1, Lemma 2.1.
-/

public section

namespace TauCeti

section Semiring

variable (F : Type*) {E V W : Type*} [CommSemiring F] [CommSemiring E] [Algebra F E]
  [AddCommMonoid V] [Module E V] [Module F V] [IsScalarTower F E V]
  [AddCommMonoid W] [Module E W] [Module F W] [IsScalarTower F E W]

/-- The centralizer `Z(φ)` of a `σ`-semilinear map `φ : V → V`: the `E`-linear endomorphisms of
`V` commuting with `φ`, as an `F`-subalgebra of `Module.End E V` for an `F`-algebra `E` on which
`σ` fixes the image of `F`. -/
def semilinearCentralizer (σ : E →+* E) (hσ : ∀ a : F, σ (algebraMap F E a) = algebraMap F E a)
    (φ : V →ₛₗ[σ] V) : Subalgebra F (Module.End E V) where
  carrier := {f | ∀ v, f (φ v) = φ (f v)}
  mul_mem' {f g} hf hg v := by
    simp only [Set.mem_ofPred_eq] at hf hg ⊢
    simp [hf, hg]
  add_mem' {f g} hf hg v := by
    simp only [Set.mem_ofPred_eq] at hf hg ⊢
    simp [hf, hg]
  algebraMap_mem' a v := by
    simp only [Module.algebraMap_end_apply]
    rw [← algebraMap_smul E a v, φ.map_smulₛₗ, hσ, algebraMap_smul]

variable {F}
variable {σ : E →+* E} {hσ : ∀ a : F, σ (algebraMap F E a) = algebraMap F E a}
  {φ : V →ₛₗ[σ] V}

@[simp]
theorem mem_semilinearCentralizer_iff {f : Module.End E V} :
    f ∈ semilinearCentralizer F σ hσ φ ↔ ∀ v, f (φ v) = φ (f v) :=
  Iff.rfl

/-- Membership in `Z(φ)` as an equality of `σ`-semilinear maps: `f ∘ φ = φ ∘ f`. -/
theorem mem_semilinearCentralizer_iff_comp {f : Module.End E V} :
    f ∈ semilinearCentralizer F σ hσ φ ↔ f ∘ₛₗ φ = φ ∘ₛₗ f := by
  simp [LinearMap.ext_iff]

variable (F) in
/-- For `σ = id`, the semilinear centralizer is the centralizer of `φ` in `Module.End E V`. -/
theorem semilinearCentralizer_id (φ : Module.End E V) :
    semilinearCentralizer F (RingHom.id E) (fun _ ↦ rfl) φ = Subalgebra.centralizer F {φ} := by
  ext f
  rw [mem_semilinearCentralizer_iff, Subalgebra.mem_centralizer_iff, Set.forall_mem_singleton]
  simp [LinearMap.ext_iff, eq_comm]

variable (F) in
/-- Multiplication by `a` on `E` commutes with `σ` exactly when `σ a = a`; so `Z(φ)` is not an
`E`-submodule of `Module.End E V` in general. -/
theorem mulLeft_mem_semilinearCentralizer_iff (a : E) :
    LinearMap.mulLeft E a ∈ semilinearCentralizer F σ hσ σ.toSemilinearMap ↔ σ a = a := by
  refine ⟨fun h ↦ ?_, fun h x ↦ by simp [h]⟩
  simpa [eq_comm] using h 1

/-- Conjugating by a linear equivalence `u : V ≃ W` carries `Z(φ)` onto `Z(u φ u⁻¹)`. -/
theorem map_conjAlgEquiv_semilinearCentralizer (u : V ≃ₗ[E] W) :
    (semilinearCentralizer F σ hσ φ).map (u.conjAlgEquiv F).toAlgHom =
      semilinearCentralizer F σ hσ
        ((u : V →ₗ[E] W) ∘ₛₗ φ ∘ₛₗ (u.symm : W →ₗ[E] V)) := by
  ext g
  simp only [Subalgebra.mem_map, mem_semilinearCentralizer_iff, LinearMap.coe_comp,
    Function.comp_apply, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨f, hf, rfl⟩ w
    simp [LinearEquiv.conjAlgEquiv_apply, hf]
  · intro hg
    refine ⟨(u.conjAlgEquiv F).symm g, fun v ↦ ?_, by simp⟩
    simp only [LinearEquiv.symm_conjAlgEquiv, LinearEquiv.conjAlgEquiv_apply, LinearMap.coe_comp,
      LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.symm_symm, LinearEquiv.symm_apply_eq]
    simpa using hg (u v)

end Semiring

section Descent

variable {F E V : Type*} [CommRing F] [Field E] [Algebra F E]
  [AddCommGroup V] [Module E V] [Module F V] [IsScalarTower F E V]
  {σ : E →+* E} {hσ : ∀ a : F, σ (algebraMap F E a) = algebraMap F E a} {φ : V →ₛₗ[σ] V}

/-- **Descent for the semilinear centralizer.** If every element of `E` fixed by `σ` comes from
`F` and `φ` is surjective, a family in `Z(φ)` that is linearly independent over `F` is linearly
independent over `E` in `Module.End E V`. -/
theorem linearIndependent_of_semilinearCentralizer
    (hfix : ∀ x : E, σ x = x → x ∈ (algebraMap F E).range) (hφ : Function.Surjective φ)
    {ι : Type*} {f : ι → semilinearCentralizer F σ hσ φ} (hf : LinearIndependent F f) :
    LinearIndependent E fun i ↦ (f i : Module.End E V) := by
  -- `g ↦ φ ∘ g` is `σ`-semilinear, `g ↦ g ∘ φ` is linear and injective, and they agree on `Z(φ)`.
  let P : Module.End E V →ₛₗ[σ] V → V :=
    { toFun g := φ ∘ g
      map_add' g h := by ext; simp
      map_smul' a g := by ext; simp }
  let Q : Module.End E V →ₗ[E] V → V :=
    { toFun g := g ∘ φ
      map_add' g h := by ext; simp
      map_smul' a g := by ext; simp }
  have hQ : Function.Injective Q := fun g h hgh ↦
    LinearMap.ext fun v ↦ by
      obtain ⟨w, rfl⟩ := hφ v
      exact congr_fun hgh w
  refine LinearIndependent.extend_scalars_of_semilinear_eq hfix P Q hQ
    (fun i ↦ funext fun v ↦ (mem_semilinearCentralizer_iff.1 (f i).property v).symm) ?_
  exact hf.map' (semilinearCentralizer F σ hσ φ).toSubmodule.subtype
    (Submodule.ker_subtype _)

end Descent

section Dimension

variable {F E V : Type*} [Field F] [Field E] [Algebra F E]
  [AddCommGroup V] [Module E V] [Module F V] [IsScalarTower F E V]
  {σ : E →+* E} {hσ : ∀ a : F, σ (algebraMap F E a) = algebraMap F E a} {φ : V →ₛₗ[σ] V}

/-- **Dimension of the semilinear centralizer** (Lawrence–Venkatesh, Lemma 2.1): if every element
of `E` fixed by `σ` comes from `F` and `φ` is surjective, then `dim_F Z(φ) ≤ (dim_E V)²`, as a
bound on the rank. -/
theorem rank_semilinearCentralizer_le [FiniteDimensional E V]
    (hfix : ∀ x : E, σ x = x → x ∈ (algebraMap F E).range) (hφ : Function.Surjective φ) :
    Module.rank F (semilinearCentralizer F σ hσ φ) ≤ (Module.finrank E V ^ 2 : ℕ) := by
  refine rank_le fun s hs ↦ ?_
  have h := (linearIndependent_of_semilinearCentralizer hfix hφ hs).fintype_card_le_finrank
  rwa [Fintype.card_coe, Module.finrank_linearMap, ← sq] at h

/-- The semilinear centralizer is finite-dimensional over `F` when `V` is finite-dimensional over
`E`, every element of `E` fixed by `σ` comes from `F` and `φ` is surjective. -/
theorem finiteDimensional_semilinearCentralizer [FiniteDimensional E V]
    (hfix : ∀ x : E, σ x = x → x ∈ (algebraMap F E).range) (hφ : Function.Surjective φ) :
    FiniteDimensional F (semilinearCentralizer F σ hσ φ) :=
  Module.rank_lt_aleph0_iff.1 <|
    (rank_semilinearCentralizer_le hfix hφ).trans_lt Cardinal.natCast_lt_aleph0

/-- **Dimension of the semilinear centralizer** (Lawrence–Venkatesh, Lemma 2.1): if every element
of `E` fixed by `σ` comes from `F` and `φ` is surjective, then `dim_F Z(φ) ≤ (dim_E V)²`. -/
theorem finrank_semilinearCentralizer_le [FiniteDimensional E V]
    (hfix : ∀ x : E, σ x = x → x ∈ (algebraMap F E).range) (hφ : Function.Surjective φ) :
    Module.finrank F (semilinearCentralizer F σ hσ φ) ≤ Module.finrank E V ^ 2 :=
  Module.finrank_le_of_rank_le (rank_semilinearCentralizer_le hfix hφ)

end Dimension

end TauCeti
