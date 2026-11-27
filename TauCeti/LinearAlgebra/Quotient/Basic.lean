/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.FiveLemma

/-!
# Basic facts about quotient modules

A surjective linear map `f : M → M₂` sending `p` into `q` induces a surjective map
`M ⧸ p → M₂ ⧸ q`, and the induced map is injective exactly when `f⁻¹(q) ≤ p`. The quotient by a
submodule is torsion-free exactly when the submodule is saturated, that is, contains every element
of which it contains a multiple by a regular scalar.

## Main results

* `Submodule.mapQ_surjective`: induced maps on quotients preserve surjectivity.
* `Submodule.mapQ_injective_iff`: the map `M ⧸ p → M₂ ⧸ q` induced by `f` is injective exactly
  when `f⁻¹(q) ≤ p`.
* `Submodule.isTorsionFree_quotient_iff`: a submodule has torsion-free quotient if and only if
  it is saturated.
-/

public section

namespace Submodule

variable {R M R₂ M₂ : Type*} [Ring R] [AddCommGroup M] [Module R M] [Ring R₂] [AddCommGroup M₂]
  [Module R₂ M₂] {τ₁₂ : R →+* R₂} (p : Submodule R M) (q : Submodule R₂ M₂)

/-- Surjectivity of a linear map implies surjectivity of the map it induces on quotients. -/
theorem mapQ_surjective (f : M →ₛₗ[τ₁₂] M₂) (h : p ≤ comap f q) (hf : Function.Surjective f) :
    Function.Surjective (p.mapQ q f h) := by
  rintro ⟨y⟩
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨Quotient.mk x, rfl⟩

/-- The map `M ⧸ p → M₂ ⧸ q` induced by `f` is injective exactly when the inverse image of `q`
under `f` lies in `p`. -/
theorem mapQ_injective_iff (f : M →ₛₗ[τ₁₂] M₂) (h : p ≤ comap f q) :
    Function.Injective (p.mapQ q f h) ↔ comap f q ≤ p := by
  rw [← LinearMap.ker_eq_bot, ker_mapQ, ← le_bot_iff, map_le_iff_le_comap, comap_bot, ker_mkQ]

/-- The quotient by a submodule is torsion-free if and only if the submodule contains every
element of which it contains a multiple by a regular scalar. Over a domain the regular scalars
are exactly the nonzero ones, see `isRegular_iff_ne_zero`. -/
theorem isTorsionFree_quotient_iff {S : Submodule R M} :
    Module.IsTorsionFree R (M ⧸ S) ↔ ∀ (c : R) (z : M), IsRegular c → c • z ∈ S → z ∈ S :=
  ⟨fun _ c _ hc ↦ (isSMulRegular_quotient_iff_mem_of_smul_mem S c).mp hc.isSMulRegular _,
    fun hS ↦ ⟨fun c hc ↦ (isSMulRegular_quotient_iff_mem_of_smul_mem S c).mpr (hS c · hc)⟩⟩

end Submodule

namespace LinearMap

open Function Set

universe u

variable {R : Type*} {M : Type u} [Ring R] [AddCommGroup M] [Module R M] {σ : R →+* R}
  {F : M →ₛₗ[σ] M}

/-- Restricting to a stable submodule preserves stability of the pulled-back submodule. -/
theorem mapsTo_restrict_comap_subtype {P Q : Submodule R M}
    (hP : MapsTo F P P) (hQ : MapsTo F Q Q) :
    MapsTo (F.restrict hP) (Q.comap P.subtype) (Q.comap P.subtype) := by
  intro x hx
  apply Submodule.mem_comap.mpr
  rw [Submodule.subtype_apply, coe_restrict_apply hP]
  exact hQ (Submodule.mem_comap.mp hx)

/-- The map induced by a semilinear endomorphism on the quotient of a stable submodule
`P` by its intersection with another stable submodule `Q`. -/
def subquotientMap (F : M →ₛₗ[σ] M) (P Q : Submodule R M)
    (hP : MapsTo F P P) (hQ : MapsTo F Q Q) :
    (P ⧸ Q.comap P.subtype) →ₛₗ[σ] (P ⧸ Q.comap P.subtype) :=
  (Q.comap P.subtype).mapQ _ (F.restrict hP) (mapsTo_restrict_comap_subtype hP hQ)

/-- The stable subquotient map is the quotient map induced by the restriction to its numerator. -/
theorem subquotientMap_eq_mapQ (F : M →ₛₗ[σ] M) (P Q : Submodule R M)
    (hP : MapsTo F P P) (hQ : MapsTo F Q Q) :
    F.subquotientMap P Q hP hQ =
      (Q.comap P.subtype).mapQ (Q.comap P.subtype) (F.restrict hP)
        (mapsTo_restrict_comap_subtype hP hQ) :=
  (rfl)

/-- The stable subquotient map sends the class of a vector to the class of its image. -/
@[simp]
theorem subquotientMap_mk (P Q : Submodule R M)
    (hP : MapsTo F P P) (hQ : MapsTo F Q Q) (x : P) :
    F.subquotientMap P Q hP hQ (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (F.restrict hP x) :=
  (rfl)

/-- The induced map on a stable subquotient is bijective if the endomorphism is surjective
on the numerator and reflects membership in the denominator within the numerator. -/
theorem bijective_subquotientMap (P Q : Submodule R M)
    (hP : MapsTo F P P) (hQ : MapsTo F Q Q)
    (hs : SurjOn F P P) (hi : ∀ x ∈ P, F x ∈ Q → x ∈ Q) :
    Bijective (F.subquotientMap P Q hP hQ) := by
  refine ⟨(Submodule.mapQ_injective_iff _ _ _ _).mpr ?_,
    Submodule.mapQ_surjective _ _ _ _ (hP.restrict_surjective_iff.mpr hs)⟩
  intro x hx
  simpa only [Submodule.mem_comap, Submodule.subtype_apply] using
    hi x x.property (by
      simpa only [Submodule.mem_comap, Submodule.subtype_apply, coe_restrict_apply hP] using hx)

/-- The equivalence between a submodule of `P` pulled back along the inclusion and the
original submodule intertwines the two restrictions of the same endomorphism. -/
theorem semiconj_comapSubtypeEquivOfLe_restrict {P Q : Submodule R M} (hle : Q ≤ P)
    (hP : MapsTo F P P) (hQ : MapsTo F Q Q) :
    Semiconj (Submodule.comapSubtypeEquivOfLe hle)
      ((F.restrict hP).restrict (mapsTo_restrict_comap_subtype hP hQ)) (F.restrict hQ) := by
  intro x
  apply Subtype.ext
  rw [Submodule.comapSubtypeEquivOfLe_apply_coe hle,
    coe_restrict_apply hQ, Submodule.comapSubtypeEquivOfLe_apply_coe hle]
  exact (congrArg Subtype.val (coe_restrict_apply (mapsTo_restrict_comap_subtype hP hQ) x)).trans
    (coe_restrict_apply hP _)

/-- Bijectivity on a stable submodule and its quotient implies bijectivity on the module. -/
theorem bijective_of_restrict_of_mapQ (P : Submodule R M) (hP : MapsTo F P P)
    (h₁ : Bijective (F.restrict hP)) (h₂ : Bijective (P.mapQ P F (fun _ hx ↦ hP hx))) :
    Bijective F := by
  have he := exact_subtype_mkQ P
  have hi : P.subtype.toAddMonoidHom.comp (F.restrict hP).toAddMonoidHom =
      F.toAddMonoidHom.comp P.subtype.toAddMonoidHom := rfl
  have hq : P.mkQ.toAddMonoidHom.comp F.toAddMonoidHom =
      (P.mapQ P F (fun _ hx ↦ hP hx)).toAddMonoidHom.comp P.mkQ.toAddMonoidHom := rfl
  exact AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (0 : PUnit.{1} →+ P) P.subtype.toAddMonoidHom P.mkQ.toAddMonoidHom (0 : (M ⧸ P) →+ PUnit.{1})
    (0 : PUnit.{1} →+ P) P.subtype.toAddMonoidHom P.mkQ.toAddMonoidHom (0 : (M ⧸ P) →+ PUnit.{1})
    (0 : PUnit.{1} →+ PUnit.{1}) (F.restrict hP).toAddMonoidHom F.toAddMonoidHom
    (P.mapQ P F (fun _ hx ↦ hP hx)).toAddMonoidHom (0 : PUnit.{1} →+ PUnit.{1})
    (by simp) hi hq (by simp)
    (fun x ↦ by simp [eq_comm]) he (fun x ↦ by simp [P.mkQ_surjective.range_eq])
    (fun x ↦ by simp [eq_comm]) he (fun x ↦ by simp [P.mkQ_surjective.range_eq])
    (bijective_of_subsingleton _).2 h₁ h₂ (injective_of_subsingleton _)

/-- A property of semilinear endomorphisms that holds on zero modules, is invariant under
linear conjugacy, and is closed under extensions can be checked on the successive quotients
of a finite descending stable filtration. -/
theorem restrict_of_filtration (F : M →ₛₗ[σ] M)
    (Φ : ∀ {N : Type u} [AddCommGroup N] [Module R N], (N →ₛₗ[σ] N) → Prop)
    (hzero : ∀ {N : Type u} [AddCommGroup N] [Module R N] [Subsingleton N]
      (g : N →ₛₗ[σ] N), Φ g)
    (hconj : ∀ {N N' : Type u} [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
      {g : N →ₛₗ[σ] N} {g' : N' →ₛₗ[σ] N'} (e : N ≃ₗ[R] N'), Semiconj e g g' → Φ g' → Φ g)
    (hext : ∀ {N : Type u} [AddCommGroup N] [Module R N] {g : N →ₛₗ[σ] N}
      (Q : Submodule R N) (hQ : MapsTo g Q Q),
      Φ (g.restrict hQ) → Φ (Q.mapQ Q g hQ) → Φ g)
    (P : ℕ → Submodule R M)
    (hP : ∀ i, MapsTo F (P i) (P i)) (hdesc : Antitone P) {n : ℕ} (hbot : P n = ⊥)
    (hgraded : ∀ i < n, Φ (F.subquotientMap (P i) (P (i + 1)) (hP i) (hP (i + 1)))) :
    Φ (F.restrict (hP 0)) := by
  have hbase : Φ (F.restrict (hP n)) := by
    have : Subsingleton (P n) := hbot ▸ inferInstance
    exact hzero _
  refine Nat.decreasingInduction (motive := fun i _ ↦ Φ (F.restrict (hP i)))
    (fun i hi ih ↦ ?_) hbase (Nat.zero_le n)
  let Q := (P (i + 1)).comap (P i).subtype
  have hQ := mapsTo_restrict_comap_subtype (hP i) (hP (i + 1))
  let hle := hdesc (Nat.le_succ i)
  exact hext Q hQ
    (hconj (Submodule.comapSubtypeEquivOfLe hle)
      (semiconj_comapSubtypeEquivOfLe_restrict hle (hP i) (hP (i + 1))) ih)
    (by simpa only [subquotientMap_eq_mapQ] using hgraded i hi)

/-- Bijectivity on the successive quotients of a finite descending stable filtration
implies bijectivity on its initial submodule. -/
theorem bijective_restrict_of_filtration (P : ℕ → Submodule R M)
    (hP : ∀ i, MapsTo F (P i) (P i)) (hdesc : Antitone P) {n : ℕ} (hbot : P n = ⊥)
    (hbij : ∀ i < n, Bijective (F.subquotientMap (P i) (P (i + 1)) (hP i) (hP (i + 1)))) :
    Bijective (F.restrict (hP 0)) := by
  refine F.restrict_of_filtration (fun g ↦ Bijective g) (fun g ↦ bijective_of_subsingleton g)
    ?_ (fun Q hQ ↦ bijective_of_restrict_of_mapQ Q hQ) P hP hdesc hbot hbij
  intro N N' _ _ _ _ g g' e he hg'
  rw [← Function.Bijective.of_comp_iff' e.bijective, he.comp_eq]
  exact hg'.comp e.bijective

end LinearMap
