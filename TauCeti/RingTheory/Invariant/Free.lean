/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.Smooth.Fiber
public import Mathlib.RingTheory.Unramified.Finite
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import TauCeti.RingTheory.Invariant.Basic

/-!
# Free actions of finite groups on rings

Let a finite group `G` act on a commutative `R`-algebra `A` by `R`-algebra automorphisms, and
suppose that `R` is the ring of invariants (`Algebra.IsInvariant R A G`), for instance
`R = Aᴳ`. The action of `G` on `Spec A` is **free** when no `g ≠ 1` fixes a geometric point. The
fixed locus of `g` is the closed subscheme cut out by the elements `g • a - a`, so freeness says
that for every `g ≠ 1` these elements generate the unit ideal of `A`.

This file proves the theorem of Chase, Harrison and Rosenberg that a free action makes `A` a
Galois extension of `R` with group `G`: the map

  `A ⊗[R] A → (G → A)`,  `a ⊗ b ↦ (a * g • b)_g`

(`TauCeti.MulSemiringAction.tensorToPi`) is an isomorphism, `A` is a finite `R`-module, and `A` is
formally unramified over `R`. If moreover `R → A` is injective, as for `R = Aᴳ`, then `A` is a
projective, faithfully flat and étale `R`-algebra. Geometrically, `Spec A → Spec Aᴳ` is then a
finite étale surjection, and `Spec A ×_{Spec Aᴳ} Spec A` is the disjoint union of `|G|` copies of
`Spec A`, the copy indexed by `g` mapping by the identity to the first factor and by the
automorphism induced by `g` to the second. This is the input that makes the affine invariant
quotient by a free action of a finite group a finite locally free quotient.

Surjectivity of `tensorToPi` is equivalent to freeness, for any `R`
(`TauCeti.MulSemiringAction.tensorToPi_surjective_iff`). Freeness gives, for each `g ≠ 1`, an
element of `A ⊗[R] A` whose components at `1` and at `g` are `1` and `0`, and the product of
these elements over all `g ≠ 1` maps to the indicator function of `1`. Writing that product as
`∑ i, xᵢ ⊗ yᵢ`, so that `∑ i, xᵢ * g • yᵢ` is `1` for `g = 1` and `0` otherwise, every `b : A` is
`b = ∑ i, (∑ g, g • (yᵢ * b)) * xᵢ`, where each `∑ g, g • (yᵢ * b)` is invariant and so comes from
`R`. This identity shows that `A` is a finite `R`-module and that `tensorToPi` is injective. When
`R → A` is injective the coefficients `∑ g, g • (yᵢ * b)` have unique, hence `R`-linear,
preimages in `R`, so the identity is a finite dual basis of `A` over `R` and `A` is projective.

## Main definitions

* `TauCeti.MulSemiringAction.tensorToPi R A G`: the `A`-algebra map
  `A ⊗[R] A →ₐ[A] (G → A)`, `a ⊗ b ↦ (a * g • b)_g`.

## Main results

* `TauCeti.MulSemiringAction.tensorToPi_surjective_iff`: `tensorToPi` is surjective exactly when
  the action is free.
* `TauCeti.MulSemiringAction.tensorToPi_bijective`: for a free action with invariant ring `R`,
  `tensorToPi` is bijective.
* `TauCeti.MulSemiringAction.moduleFinite`, `TauCeti.MulSemiringAction.projective`,
  `TauCeti.MulSemiringAction.faithfullyFlat`: for a free action with invariant ring `R`, `A` is
  a finite `R`-module, and if `R → A` is injective it is projective and faithfully flat.
* `TauCeti.MulSemiringAction.formallyUnramified`, `TauCeti.MulSemiringAction.etale`: `A` is
  formally unramified over `R`, and étale if `R → A` is injective.

## References

* S. U. Chase, D. K. Harrison and A. Rosenberg, *Galois theory and Galois cohomology of
  commutative rings*, Mem. Amer. Math. Soc. **52** (1965), 15–33, Theorem 1.3.
* M. Demazure and A. Grothendieck, *Schémas en groupes (SGA 3)*, Exposé V, §4.
-/

public section

open TensorProduct

namespace TauCeti.MulSemiringAction

variable (R A G : Type*) [CommRing R] [CommRing A] [Algebra R A] [Group G]
  [MulSemiringAction G A] [SMulCommClass G R A]

/-- The `A`-algebra map `A ⊗[R] A → (G → A)` sending `a ⊗ b` to `g ↦ a * g • b`. When `G` is
finite, on spectra it is the morphism from the disjoint union of `|G|` copies of `Spec A` to
`Spec A ×_{Spec R} Spec A` whose `g`-th component is the identity on the first factor and the
automorphism of `Spec A` induced by `g` on the second. -/
noncomputable def tensorToPi : A ⊗[R] A →ₐ[A] (G → A) :=
  AlgHom.pi fun g ↦ Algebra.TensorProduct.lift (AlgHom.id A A)
    (MulSemiringAction.toAlgHom R A g) fun _ _ ↦ Commute.all _ _

variable {R A G}

@[simp]
theorem tensorToPi_tmul (a b : A) (g : G) : tensorToPi R A G (a ⊗ₜ b) g = a * g • b := (rfl)

/-- The component of `tensorToPi` at the identity is multiplication `A ⊗[R] A → A`. -/
theorem tensorToPi_apply_one (z : A ⊗[R] A) :
    tensorToPi R A G z 1 = Algebra.TensorProduct.lmul' R z := by
  induction z using TensorProduct.inductionOn with
  | tmul a b => simp
  | add x y hx hy => simp [hx, hy]

/-- Twisting the right factor by `k` shifts the components of `tensorToPi` by `k`. -/
theorem tensorToPi_map_toAlgHom (k : G) (z : A ⊗[R] A) (g : G) :
    tensorToPi R A G
        (Algebra.TensorProduct.map (AlgHom.id R A) (MulSemiringAction.toAlgHom R A k) z) g =
      tensorToPi R A G z (g * k) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b => simp [mul_smul]
  | add x y hx hy => simp [hx, hy]

/-- If `g • a - a` generate the unit ideal, some element of `A ⊗[R] A` has components `1` at the
identity and `0` at `g`. -/
private theorem exists_tensorToPi_one_eq_one_and_eq_zero {g : G}
    (hg : Ideal.span (Set.range fun a : A ↦ g • a - a) = ⊤) :
    ∃ u : A ⊗[R] A, tensorToPi R A G u 1 = 1 ∧ tensorToPi R A G u g = 0 := by
  -- The differences of the components at `g` and at `1` form an ideal containing every
  -- `g • a - a = tensorToPi (1 ⊗ a) g - tensorToPi (1 ⊗ a) 1`, hence containing `1`.
  let ψ : A ⊗[R] A →ₗ[A] A := LinearMap.proj g ∘ₗ (tensorToPi R A G).toLinearMap -
    LinearMap.proj 1 ∘ₗ (tensorToPi R A G).toLinearMap
  have hle : Ideal.span (Set.range fun a : A ↦ g • a - a) ≤ LinearMap.range ψ :=
    Ideal.span_le.mpr <| by
      rintro _ ⟨a, rfl⟩
      exact ⟨1 ⊗ₜ a, by simp [ψ]⟩
  obtain ⟨v, hv⟩ := hle (x := 1) (by rw [hg]; exact Submodule.mem_top)
  refine ⟨algebraMap A _ (tensorToPi R A G v g) - v, ?_, by simp⟩
  simpa [ψ] using hv

/-- For a free action of a finite group, some element of `A ⊗[R] A` maps to the indicator function
of the identity under `tensorToPi`. -/
private theorem exists_tensorToPi_eq_single [Finite G] [DecidableEq G]
    (hG : ∀ g : G, g ≠ 1 → Ideal.span (Set.range fun a : A ↦ g • a - a) = ⊤) :
    ∃ u : A ⊗[R] A, tensorToPi R A G u = Pi.single 1 1 := by
  classical
  have := Fintype.ofFinite G
  choose u hu₁ hu using fun g : {g : G // g ≠ 1} ↦
    exists_tensorToPi_one_eq_one_and_eq_zero (R := R) (hG g g.2)
  refine ⟨∏ g, u g, funext fun h ↦ ?_⟩
  rw [map_prod, Finset.prod_apply]
  by_cases hh : h = 1
  · subst hh
    simp [hu₁]
  · rw [Pi.single_eq_of_ne hh]
    exact Finset.prod_eq_zero (i := ⟨h, hh⟩) (Finset.mem_univ _) (hu ⟨h, hh⟩)

/-- An element of `A ⊗[R] A` mapping to the indicator function of the identity forces every
`g ≠ 1` to act freely. -/
private theorem span_eq_top_of_tensorToPi_eq_single [DecidableEq G] {u : A ⊗[R] A}
    (hu : tensorToPi R A G u = Pi.single 1 1) {g : G} (hg : g ≠ 1) :
    Ideal.span (Set.range fun a : A ↦ g • a - a) = ⊤ := by
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset u
  have h₁ := congr_fun hu 1
  have hg' := congr_fun hu g
  simp only [map_sum, Finset.sum_apply, tensorToPi_tmul, one_smul, Pi.single_eq_same] at h₁
  simp only [map_sum, Finset.sum_apply, tensorToPi_tmul, Pi.single_eq_of_ne hg] at hg'
  -- `1 = ∑ xᵢ * yᵢ - ∑ xᵢ * g • yᵢ = -∑ xᵢ * (g • yᵢ - yᵢ)`.
  have h : (1 : A) = -∑ p ∈ S, p.1 * (g • p.2 - p.2) := by
    simp only [mul_sub, Finset.sum_sub_distrib, hg', h₁]
    ring
  rw [Ideal.eq_top_iff_one, h]
  exact neg_mem <| Ideal.sum_mem _ fun p _ ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨p.2, rfl⟩)

/-- **Chase–Harrison–Rosenberg.** For a finite group, `tensorToPi` is surjective exactly when the
action is free: for every `g ≠ 1`, the elements `g • a - a` generate the unit ideal. -/
theorem tensorToPi_surjective_iff [Finite G] :
    Function.Surjective (tensorToPi R A G) ↔
      ∀ g : G, g ≠ 1 → Ideal.span (Set.range fun a : A ↦ g • a - a) = ⊤ := by
  classical
  refine ⟨fun h g hg ↦ ?_, fun hG f ↦ ?_⟩
  · obtain ⟨u, hu⟩ := h (Pi.single 1 1)
    exact span_eq_top_of_tensorToPi_eq_single hu hg
  have := Fintype.ofFinite G
  obtain ⟨u, hu⟩ := exists_tensorToPi_eq_single (R := R) hG
  -- Twisting `u` by `h⁻¹` moves the indicator function of `1` to that of `h`.
  have hw (h : G) : tensorToPi R A G
      (Algebra.TensorProduct.map (AlgHom.id R A) (MulSemiringAction.toAlgHom R A h⁻¹) u) =
        Pi.single h 1 := by
    ext g
    rw [tensorToPi_map_toAlgHom, hu]
    simp [Pi.single_apply, mul_inv_eq_one]
  refine ⟨∑ h, f h •
    Algebra.TensorProduct.map (AlgHom.id R A) (MulSemiringAction.toAlgHom R A h⁻¹) u, ?_⟩
  simp only [map_sum, map_smul, hw]
  ext g
  simp [Pi.single_apply]

/-- The finite family attached to a preimage of the indicator function of `1` under
`tensorToPi`. -/
private theorem exists_finset_sum_mul_smul [DecidableEq G] {u : A ⊗[R] A}
    (hu : tensorToPi R A G u = Pi.single 1 1) :
    ∃ S : Finset (A × A), ∀ g : G, ∑ p ∈ S, p.1 * g • p.2 = (Pi.single 1 1 : G → A) g := by
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset u
  exact ⟨S, fun g ↦ by simpa using congr_fun hu g⟩

/-- The dual basis identity `b = ∑ i, (∑ g, g • (yᵢ * b)) * xᵢ`. -/
private theorem sum_sum_smul_mul [Fintype G] [DecidableEq G] {S : Finset (A × A)}
    (hS : ∀ g : G, ∑ p ∈ S, p.1 * g • p.2 = (Pi.single 1 1 : G → A) g) (b : A) :
    ∑ p ∈ S, (∑ g : G, g • (p.2 * b)) * p.1 = b := by
  have h (g : G) : ∑ p ∈ S, g • (p.2 * b) * p.1 = (Pi.single 1 1 : G → A) g * g • b := by
    rw [← hS g, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [smul_mul']
    ring
  calc ∑ p ∈ S, (∑ g : G, g • (p.2 * b)) * p.1
      = ∑ g : G, ∑ p ∈ S, g • (p.2 * b) * p.1 := by
        simp only [Finset.sum_mul]
        exact Finset.sum_comm
    _ = b := by
        simp only [h]
        simp [Pi.single_apply]

section Invariant

variable [Algebra.IsInvariant R A G]

omit [SMulCommClass G R A] in
/-- An invariant element of `A` passes through the tensor product over the invariant ring. -/
theorem mul_tmul_eq_tmul_mul {c : A} (hc : ∀ g : G, g • c = c) (a b : A) :
    (a * c) ⊗ₜ[R] b = a ⊗ₜ[R] (c * b) := by
  obtain ⟨r, rfl⟩ := Algebra.IsInvariant.isInvariant (A := R) (G := G) c hc
  rw [mul_comm a, ← Algebra.smul_def, ← Algebra.smul_def, smul_tmul]

/-- The inverse of `tensorToPi`, written in terms of the dual basis. -/
private theorem sum_tmul_eq [Fintype G] [DecidableEq G] {S : Finset (A × A)}
    (hS : ∀ g : G, ∑ p ∈ S, p.1 * g • p.2 = (Pi.single 1 1 : G → A) g) (z : A ⊗[R] A) :
    ∑ p ∈ S, (∑ g : G, g • p.2 * tensorToPi R A G z g) ⊗ₜ[R] p.1 = z := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    calc ∑ p ∈ S, (∑ g : G, g • p.2 * tensorToPi R A G (a ⊗ₜ b) g) ⊗ₜ[R] p.1
        = ∑ p ∈ S, (a * ∑ g : G, g • (p.2 * b)) ⊗ₜ[R] p.1 := by
          refine Finset.sum_congr rfl fun p _ ↦ ?_
          simp only [tensorToPi_tmul, Finset.mul_sum, smul_mul']
          congr 1
          exact Finset.sum_congr rfl fun g _ ↦ by ring
      _ = ∑ p ∈ S, a ⊗ₜ[R] ((∑ g : G, g • (p.2 * b)) * p.1) :=
          Finset.sum_congr rfl fun p _ ↦ mul_tmul_eq_tmul_mul (smul_sum_smul · _) _ _
      _ = a ⊗ₜ b := by rw [← tmul_sum, sum_sum_smul_mul hS]
  | add x y hx hy =>
    simp only [map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib, add_tmul]
    rw [hx, hy]

/-- **Chase–Harrison–Rosenberg.** For a free action of a finite group with invariant ring `R`,
`tensorToPi : A ⊗[R] A → (G → A)` is bijective. -/
theorem tensorToPi_bijective [Finite G]
    (hG : ∀ g : G, g ≠ 1 → Ideal.span (Set.range fun a : A ↦ g • a - a) = ⊤) :
    Function.Bijective (tensorToPi R A G) := by
  classical
  have := Fintype.ofFinite G
  refine ⟨(injective_iff_map_eq_zero _).mpr fun z hz ↦ ?_, tensorToPi_surjective_iff.mpr hG⟩
  obtain ⟨u, hu⟩ := exists_tensorToPi_eq_single (R := R) hG
  obtain ⟨S, hS⟩ := exists_finset_sum_mul_smul hu
  rw [← sum_tmul_eq hS z, hz]
  simp

/-- For a free action of a finite group with invariant ring `R`, `A` is a finite `R`-module. -/
theorem moduleFinite [Finite G]
    (hG : ∀ g : G, g ≠ 1 → Ideal.span (Set.range fun a : A ↦ g • a - a) = ⊤) :
    Module.Finite R A := by
  classical
  have := Fintype.ofFinite G
  obtain ⟨u, hu⟩ := exists_tensorToPi_eq_single (R := R) hG
  obtain ⟨S, hS⟩ := exists_finset_sum_mul_smul hu
  refine ⟨⟨S.image Prod.fst, eq_top_iff.mpr fun b _ ↦ ?_⟩⟩
  rw [← sum_sum_smul_mul hS b]
  refine Submodule.sum_mem _ fun p hp ↦ ?_
  obtain ⟨r, hr⟩ := Algebra.IsInvariant.isInvariant (A := R) _ (smul_sum_smul (G := G) · (p.2 * b))
  rw [← hr, ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_image_of_mem _ hp))

/-- For a free action of a finite group with invariant ring `R`, if `R → A` is injective then `A`
is a projective `R`-module. -/
theorem projective [Finite G] [FaithfulSMul R A]
    (hG : ∀ g : G, g ≠ 1 → Ideal.span (Set.range fun a : A ↦ g • a - a) = ⊤) :
    Module.Projective R A := by
  classical
  have := Fintype.ofFinite G
  obtain ⟨u, hu⟩ := exists_tensorToPi_eq_single (R := R) hG
  obtain ⟨S, hS⟩ := exists_finset_sum_mul_smul hu
  -- The coordinate `b ↦ ∑ g, g • (y * b)` of the dual basis, as an `R`-linear map `A → R`.
  choose φ hφ using fun y b : A ↦
    Algebra.IsInvariant.isInvariant (A := R) _ (smul_sum_smul (G := G) · (y * b))
  have inj := FaithfulSMul.algebraMap_injective R A
  let f (y : A) : A →ₗ[R] R :=
    { toFun := φ y
      map_add' b b' := inj <| by simp [hφ, mul_add, Finset.sum_add_distrib]
      map_smul' r b := inj <| by
        simp only [hφ, mul_smul_comm, smul_comm _ r, ← Finset.smul_sum]
        simp only [RingHom.id_apply, smul_eq_mul, map_mul, hφ, Algebra.smul_def] }
  refine .of_split (LinearMap.pi fun p : S ↦ f p.1.2)
    (Fintype.linearCombination R fun p : S ↦ p.1.1) (LinearMap.ext fun b ↦ ?_)
  simp only [LinearMap.comp_apply, Fintype.linearCombination_apply, LinearMap.pi_apply,
    LinearMap.id_apply, Algebra.smul_def]
  simp only [f, LinearMap.coe_mk, AddHom.coe_mk, hφ]
  exact (Finset.sum_coe_sort S _).trans (sum_sum_smul_mul hS b)

/-- For a free action of a finite group with invariant ring `R`, if `R → A` is injective then `A`
is a faithfully flat `R`-module. -/
theorem faithfullyFlat [Finite G] [FaithfulSMul R A]
    (hG : ∀ g : G, g ≠ 1 → Ideal.span (Set.range fun a : A ↦ g • a - a) = ⊤) :
    Module.FaithfullyFlat R A := by
  have := projective (R := R) hG
  have := Algebra.IsInvariant.isIntegral R A G
  refine .of_comap_surjective fun P ↦ ?_
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P.asIdeal (⊥ : Ideal A)
    (by rw [Ideal.under, Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective R A)]
        exact bot_le)
  exact ⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQP⟩

/-- For a free action of a finite group with invariant ring `R`, `A` is formally unramified over
`R`. -/
theorem formallyUnramified [Finite G]
    (hG : ∀ g : G, g ≠ 1 → Ideal.span (Set.range fun a : A ↦ g • a - a) = ⊤) :
    Algebra.FormallyUnramified R A := by
  classical
  have := moduleFinite (R := R) hG
  obtain ⟨u, hu⟩ := exists_tensorToPi_eq_single (R := R) hG
  refine Algebra.FormallyUnramified.iff_exists_tensorProduct.mpr ⟨u, fun s ↦ ?_, ?_⟩
  · refine (tensorToPi_bijective hG).1 ?_
    ext g
    by_cases hg : g = 1
    · subst hg
      simp [hu]
    · simp [hu, Pi.single_eq_of_ne hg]
  · rw [← tensorToPi_apply_one (G := G), hu, Pi.single_eq_same]

/-- For a free action of a finite group with invariant ring `R`, if `R → A` is injective then `A`
is an étale `R`-algebra. -/
theorem etale [Finite G] [FaithfulSMul R A]
    (hG : ∀ g : G, g ≠ 1 → Ideal.span (Set.range fun a : A ↦ g • a - a) = ⊤) :
    Algebra.Etale R A := by
  have := moduleFinite (R := R) hG
  have := projective (R := R) hG
  have := formallyUnramified (R := R) hG
  have := Module.finitePresentation_of_projective R A
  exact .of_formallyUnramified_of_flat

end Invariant

end TauCeti.MulSemiringAction
