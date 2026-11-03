/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Adjoin.Basic
public import Mathlib.Algebra.Module.FinitePresentation

/-!
# Spreading isomorphisms from a localization

A finite type ring map with finitely generated kernel which becomes bijective after
localization is already bijective on some principal neighbourhood. In particular this applies
to finite type maps with Noetherian source. Surjectivity requires only finite type, and
injectivity requires only a finitely generated kernel; the two results are exposed separately.

These are the affine shrinking steps for spreading an isomorphism between finite algebras
over a Noetherian base from a local scheme to an open neighbourhood. They do not assert the
unrestricted finite-presentation descent theorem over non-Noetherian rings.

## References

* The Stacks Project, Lemma 32.20.3 (0BQ5), the affine shrinking argument.
-/

public section

open scoped BigOperators Pointwise

namespace RingHom

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A finite type ring map which becomes surjective after inverting a submonoid is
surjective after inverting a single element of that submonoid. -/
theorem exists_surjective_localizationAway (f : R →+* S) (hf : f.FiniteType)
    (M : Submonoid R)
    (h : Function.Surjective (IsLocalization.map (S := Localization M)
      (Localization (M.map f)) f (Submonoid.le_comap_map M))) :
    ∃ r ∈ M, Function.Surjective (Localization.awayMap f r) := by
  classical
  let : Algebra R S := f.toAlgebra
  obtain ⟨s, hs⟩ := hf
  have hgen (y : S) : ∃ t ∈ M, ∃ a : R, f t * y = f a := by
    obtain ⟨z, hz⟩ := h (algebraMap S (Localization (M.map f)) y)
    obtain ⟨a, t, rfl⟩ := IsLocalization.exists_mk'_eq M z
    have he : algebraMap S (Localization (M.map f)) (f t * y) =
        algebraMap S (Localization (M.map f)) (f a) := by
      rw [map_mul, ← hz, IsLocalization.map_mk']
      exact IsLocalization.mk'_spec' (Localization (M.map f)) (f a)
        ⟨f t, Submonoid.mem_map_of_mem _ t.2⟩
    obtain ⟨d, hd⟩ := (IsLocalization.eq_iff_exists (M.map f) _).mp he
    obtain ⟨u, hu, hdu⟩ := d.2
    rw [← hdu] at hd
    exact ⟨u * t, M.mul_mem hu t.2, u * a, by simpa [map_mul, mul_assoc] using hd⟩
  choose t ht a ha using fun y : s ↦ hgen y
  let r : R := ∏ y : s, t y
  have hr : r ∈ M := M.prod_mem fun y _ ↦ ht y
  -- One denominator puts all generators in the scalar subalgebra.
  have hsubset : r • (s : Set S) ⊆ ((⊥ : Subalgebra R S) : Set S) := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem (fun y : s ↦ t y) (Finset.mem_univ ⟨y, hy⟩)
    apply Algebra.mem_bot.mpr
    refine ⟨q * a ⟨y, hy⟩, ?_⟩
    simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, r, hq, map_mul]
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      congrArg (f q * ·) (ha ⟨y, hy⟩).symm
  refine ⟨r, hr, (IsLocalization.Away.map_surjective_iff (Localization.Away r)
    (Localization.Away (f r)) f r).mpr fun y ↦ ?_⟩
  obtain ⟨n, hn⟩ := Algebra.pow_smul_mem_of_smul_subset_of_mem_adjoin r (s : Set S)
    ⊥ hsubset (hs ▸ Algebra.mem_top (x := y)) (Subalgebra.algebraMap_mem _ _)
  obtain ⟨a, ha⟩ := Algebra.mem_bot.mp (hn n le_rfl)
  exact ⟨a, n, by simpa [Algebra.smul_def, RingHom.algebraMap_toAlgebra] using ha⟩

/-- A ring map with finitely generated kernel which becomes injective after inverting a
submonoid is injective after inverting a single element of that submonoid. No finite type
hypothesis on the target is required. -/
theorem exists_injective_localizationAway (f : R →+* S) (hker : (ker f).FG)
    (M : Submonoid R)
    (h : Function.Injective (IsLocalization.map (S := Localization M)
      (Localization (M.map f)) f (Submonoid.le_comap_map M))) :
    ∃ r ∈ M, Function.Injective (Localization.awayMap f r) := by
  have : Module.Finite R (ker f) := Module.Finite.of_fg hker
  -- The inclusion of the kernel becomes zero after localization.
  have he : (Algebra.linearMap R (Localization M)).comp (ker f).subtype =
      (Algebra.linearMap R (Localization M)).comp (0 : ker f →ₗ[R] R) := by
    ext x
    apply h
    simp [IsLocalization.map_eq, mem_ker.mp x.2]
  obtain ⟨r, hr⟩ := Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule M
    (Algebra.linearMap R (Localization M)) (ker f).subtype 0 he
  refine ⟨r, r.2, (IsLocalization.Away.map_injective_iff (S := Localization.Away (r : R))
    (Localization.Away (f r)) f r).mpr fun x hx ↦ ⟨1, ?_⟩⟩
  simpa [Submonoid.smul_def] using congrArg (fun g : ker f →ₗ[R] R ↦ g ⟨x, hx⟩) hr

/-- A finite type ring map with finitely generated kernel which becomes an isomorphism
after localization is an isomorphism on a principal neighbourhood. For a Noetherian source,
the kernel hypothesis follows from `IsNoetherian.noetherian`. -/
theorem exists_bijective_localizationAway (f : R →+* S) (hf : f.FiniteType)
    (hker : (ker f).FG) (M : Submonoid R)
    (h : Function.Bijective (IsLocalization.map (S := Localization M)
      (Localization (M.map f)) f (Submonoid.le_comap_map M))) :
    ∃ r ∈ M, Function.Bijective (Localization.awayMap f r) := by
  obtain ⟨a, ha, hinj⟩ := f.exists_injective_localizationAway hker M h.1
  obtain ⟨b, hb, hsurj⟩ := f.exists_surjective_localizationAway hf M h.2
  exact ⟨a * b, M.mul_mem ha hb,
    Localization.awayMap_injective_of_dvd f (dvd_mul_right a b) hinj,
    Localization.awayMap_surjective_of_dvd f (dvd_mul_left b a) hsurj⟩

end RingHom
