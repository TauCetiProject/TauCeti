/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Adjoin.Basic
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Spreading isomorphisms from a localization

A finite type ring map with finitely generated kernel which becomes bijective after
localization is already bijective on some principal neighbourhood. In particular this applies
to finite type maps with Noetherian source. Surjectivity requires only finite type, and
injectivity requires only a finitely generated kernel; the two results are exposed separately.

A finitely presented ring map which becomes bijective after localization also becomes
bijective on a principal neighbourhood, without a Noetherian hypothesis. Unlike the
finite-kernel criterion, this applies even when the original kernel is not finitely generated.

These are the affine shrinking steps for spreading an isomorphism from a local scheme to an
open neighbourhood. The finite-presentation criterion applies to a given map; it does not
construct a map from an isomorphism between localized algebras.

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

/-- In a commuting square with injective bottom map and a localization on the left,
a single denominator annihilates the finitely generated kernel of the top map. -/
theorem exists_mul_ker_eq_zero_of_injective_localization (f : R →+* S) (hker : (ker f).FG)
    (M : Submonoid R) {Rm T : Type*} [CommRing Rm] [CommRing T]
    [Algebra R Rm] [IsLocalization M Rm] (g : Rm →+* T) (k : S →+* T)
    (hcomm : g.comp (algebraMap R Rm) = k.comp f) (hg : Function.Injective g) :
    ∃ r : M, ∀ x ∈ ker f, (r : R) * x = 0 := by
  have : Module.Finite R (ker f) := Module.Finite.of_fg hker
  have he : (Algebra.linearMap R Rm).comp (ker f).subtype =
      (Algebra.linearMap R Rm).comp (0 : ker f →ₗ[R] R) := by
    ext x
    apply hg
    have hx := congrArg (fun l : R →+* T ↦ l x) hcomm
    simpa [mem_ker.mp x.2] using hx
  obtain ⟨r, hr⟩ := Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule M
    (Algebra.linearMap R Rm) (ker f).subtype 0 he
  exact ⟨r, fun x hx ↦ by
    simpa [Submonoid.smul_def] using congrArg (fun l : ker f →ₗ[R] R ↦ l ⟨x, hx⟩) hr⟩

/-- A ring map with finitely generated kernel which becomes injective after inverting a
submonoid is injective after inverting a single element of that submonoid. No finite type
hypothesis on the target is required. -/
theorem exists_injective_localizationAway (f : R →+* S) (hker : (ker f).FG)
    (M : Submonoid R)
    (h : Function.Injective (IsLocalization.map (S := Localization M)
      (Localization (M.map f)) f (Submonoid.le_comap_map M))) :
    ∃ r ∈ M, Function.Injective (Localization.awayMap f r) := by
  obtain ⟨r, hr⟩ := f.exists_mul_ker_eq_zero_of_injective_localization hker M
    (IsLocalization.map (Localization (M.map f)) f (Submonoid.le_comap_map M))
    (algebraMap S (Localization (M.map f))) (IsLocalization.map_comp _) h
  refine ⟨r, r.2, (IsLocalization.Away.map_injective_iff (S := Localization.Away (r : R))
    (Localization.Away (f r)) f r).mpr fun x hx ↦ ⟨1, ?_⟩⟩
  simpa using hr x hx

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

/-- If a finitely presented ring map becomes surjective after inverting `a`, then the kernel of the
resulting map between the localizations away from `a` and `f a` is finitely generated. -/
theorem FinitePresentation.fg_ker_awayMap_of_surjective {f : R →+* S} (hf : f.FinitePresentation)
    (a : R) (hsurj : Function.Surjective (Localization.awayMap f a)) :
    (ker (Localization.awayMap f a)).FG := by
  classical
  let Ra := Localization.Away a
  let Sa := Localization.Away (f a)
  let fa : Ra →+* Sa := Localization.awayMap f a
  let : Algebra Ra Sa := fa.toAlgebra
  have hRa : (algebraMap R Ra).FiniteType := .of_finitePresentation
    (finitePresentation_algebraMap.mpr (IsLocalization.Away.finitePresentation a))
  have hloc : (algebraMap S Sa).FinitePresentation :=
    finitePresentation_algebraMap.mpr (IsLocalization.Away.finitePresentation (S := Sa) (f a))
  have hcomp : (fa.comp (algebraMap R Ra)).FinitePresentation := by
    convert hloc.comp hf using 1
    ext x
    simp [fa, Sa, IsLocalization.Away.map]
  have hfa : fa.FinitePresentation := hcomp.of_comp_finiteType _ hRa
  have : Algebra.FinitePresentation Ra Sa := hfa
  exact Algebra.FinitePresentation.ker_fG_of_surjective (Algebra.ofId Ra Sa) hsurj

/-- If the localized map is injective and the kernel of the map away from `a ∈ M` is finitely
generated, one more denominator `t ∈ M` kills that whole kernel. -/
private theorem exists_mem_mul_ker_awayMap_eq_zero (f : R →+* S) (M : Submonoid R) {a : R}
    (ha : a ∈ M) (hker : (ker (Localization.awayMap f a)).FG)
    (hinj : Function.Injective (IsLocalization.map (S := Localization M)
      (Localization (M.map f)) f (Submonoid.le_comap_map M))) :
    ∃ t ∈ M, ∀ x ∈ ker (Localization.awayMap f a),
      algebraMap R (Localization.Away a) t * x = 0 := by
  classical
  let Ra := Localization.Away a
  let Sa := Localization.Away (f a)
  let fa : Ra →+* Sa := Localization.awayMap f a
  let : Algebra Ra Sa := fa.toAlgebra
  have hle : Submonoid.powers a ≤ M := (Submonoid.powers_le).mpr ha
  let : Algebra Ra (Localization M) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe Ra (Localization M) _ M hle
  let : IsScalarTower R Ra (Localization M) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le Ra (Localization M) _ M hle
  let : IsLocalization (M.map (algebraMap R Ra)) (Localization M) :=
    IsLocalization.isLocalization_of_submonoid_le Ra (Localization M) _ M hle
  let g : Localization M →+* Localization (M.map f) :=
    IsLocalization.map _ f (Submonoid.le_comap_map M)
  have hleS : Submonoid.powers (f a) ≤ M.map f :=
    Submonoid.powers_le.mpr (Submonoid.mem_map_of_mem f ha)
  let : Algebra Sa (Localization (M.map f)) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe Sa (Localization (M.map f)) _ _ hleS
  let : IsScalarTower S Sa (Localization (M.map f)) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le Sa
      (Localization (M.map f)) _ _ hleS
  obtain ⟨b, hb⟩ := fa.exists_mul_ker_eq_zero_of_injective_localization hker
    (M.map (algebraMap R Ra)) g (algebraMap Sa (Localization (M.map f)))
    (f.map_comp_algebraMap_eq_algebraMap_comp_awayMap M a) hinj
  obtain ⟨t, ht, hbt⟩ := b.2
  exact ⟨t, ht, fun x hx => hbt ▸ hb x hx⟩
/-- A finitely presented ring map which becomes an isomorphism after localization is already
an isomorphism on a principal neighbourhood. Neither ring needs to be Noetherian, and the
kernel of the original map need not be finitely generated. -/
theorem exists_bijective_localizationAway_of_finitePresentation (f : R →+* S)
    (hf : f.FinitePresentation) (M : Submonoid R)
    (h : Function.Bijective (IsLocalization.map (S := Localization M)
      (Localization (M.map f)) f (Submonoid.le_comap_map M))) :
    ∃ r ∈ M, Function.Bijective (Localization.awayMap f r) := by
  classical
  -- First shrink so that the map is surjective. Its localized kernel is then finite.
  obtain ⟨a, ha, hsurj⟩ := f.exists_surjective_localizationAway (.of_finitePresentation hf) M h.2
  have hker := hf.fg_ker_awayMap_of_surjective a hsurj
  -- One further denominator kills this finite kernel.
  obtain ⟨t, ht, hkill⟩ := exists_mem_mul_ker_awayMap_eq_zero f M ha hker h.1
  refine ⟨a * t, M.mul_mem ha ht, ?_,
    Localization.awayMap_surjective_of_dvd f (dvd_mul_right a t) hsurj⟩
  apply Localization.awayMap_injective_iff.mpr
  intro x hx
  have hxa : algebraMap R (Localization.Away a) x ∈ ker (Localization.awayMap f a) := by
    simp [mem_ker, IsLocalization.Away.map, IsLocalization.map_eq, hx]
  have hz : algebraMap R (Localization.Away a) (t * x) = 0 := by
    simpa [map_mul] using hkill _ hxa
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (.powers a) _ (t * x)).mp hz
  refine ⟨n + 1, ?_⟩
  calc
    (a * t) ^ (n + 1) * x = (a * t ^ n) * (a ^ n * (t * x)) := by ring
    _ = 0 := by simp [hn]

end RingHom
