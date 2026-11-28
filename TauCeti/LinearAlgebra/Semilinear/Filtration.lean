/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.FiveLemma

/-!
# Semilinear endomorphisms of filtered modules

A property of semilinear endomorphisms can be checked on the graded pieces of a finite stable
filtration if it holds on zero modules, is invariant under conjugacy, and is closed under
extensions. In particular, bijectivity passes from the graded pieces to the filtered module.
-/

public section

namespace LinearMap

open Function Set

universe u

variable {R : Type*} {M : Type u} [Ring R] [AddCommGroup M] [Module R M] {σ : R →+* R}
  {F : M →ₛₗ[σ] M}

/-- The equivalence between a submodule of `P` pulled back along the inclusion and the
original submodule intertwines the two restrictions of the same endomorphism. -/
theorem semiconj_comapSubtypeEquivOfLe_restrict {P Q : Submodule R M} (hle : Q ≤ P)
    (hP : MapsTo F P P) (hQ : MapsTo F Q Q) :
    Semiconj (Submodule.comapSubtypeEquivOfLe hle)
      ((F.restrict hP).restrict (p := Q.comap P.subtype) (q := Q.comap P.subtype)
        (Semiconj.mapsTo_preimage
          (coe_restrict_apply hP : Semiconj P.subtype (F.restrict hP) F) hQ))
      (F.restrict hQ) := by
  intro x
  apply Subtype.ext
  rw [Submodule.comapSubtypeEquivOfLe_apply_coe hle,
    coe_restrict_apply hQ, Submodule.comapSubtypeEquivOfLe_apply_coe hle]
  have h : MapsTo (F.restrict hP) (Q.comap P.subtype) (Q.comap P.subtype) :=
    Semiconj.mapsTo_preimage (coe_restrict_apply hP : Semiconj P.subtype (F.restrict hP) F) hQ
  exact (congrArg Subtype.val (coe_restrict_apply h x)).trans (coe_restrict_apply hP _)

/-- Bijectivity on a stable submodule and its quotient implies bijectivity on the module. -/
theorem bijective_of_restrict_of_mapQ (P : Submodule R M) (hP : MapsTo F P P)
    (h₁ : Bijective (F.restrict hP)) (h₂ : Bijective (P.mapQ P F (fun _ hx ↦ hP hx))) :
    Bijective F := by
  have he := exact_subtype_mkQ P
  have hi : P.subtype.toAddMonoidHom.comp (F.restrict hP).toAddMonoidHom =
      F.toAddMonoidHom.comp P.subtype.toAddMonoidHom := by
    ext x
    simpa only [AddMonoidHom.comp_apply, toAddMonoidHom_coe, Submodule.subtype_apply] using
      coe_restrict_apply hP x
  have hq : P.mkQ.toAddMonoidHom.comp F.toAddMonoidHom =
      (P.mapQ P F (fun _ hx ↦ hP hx)).toAddMonoidHom.comp P.mkQ.toAddMonoidHom :=
    congrArg toAddMonoidHom (Submodule.mapQ_mkQ P P F).symm
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
  have hrestrict : Semiconj (P i).subtype (F.restrict (hP i)) F := coe_restrict_apply (hP i)
  have hQ : MapsTo (F.restrict (hP i)) Q Q := hrestrict.mapsTo_preimage (hP (i + 1))
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
