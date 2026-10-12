/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Algebra.Lie.Killing.Perfect
public import TauCeti.Algebra.Lie.NilpotentExtension
public import TauCeti.Algebra.Lie.Quotient
public import TauCeti.Algebra.Lie.SemiDirect.Basic
public import TauCeti.Algebra.Lie.Solvable.Derived

/-!
# Derivations carry the solvable radical into the nilradical

Over a field of characteristic zero, every derivation of a finite-dimensional Lie algebra `L`
maps the solvable radical `radical K L` into the nilradical `nilradical K L`. In particular every
derivation of a solvable Lie algebra has image in the nilradical, the nilradical is stable under
all derivations, and `⁅L, radical K L⁆ ≤ nilradical K L`. The last inclusion gives the radical
criterion: an element of the radical with nilpotent adjoint action lies in the nilradical.
Stability under derivations gives the nilradical of an ideal: for every ideal `I` of `L`, the
nilradical of `I` consists of the elements of `I` lying in the nilradical of `L`.

These are the facts on derivation values used to refine a cofinite enveloping ideal into one
stable under all lifted derivations, without assuming that the original ideal is stable, and to
compare nilradicals along a flag of ideals between the nilradical and the radical. The radical
criterion places the radical component of an `ad`-nilpotent element in the nilradical, which is
how Hochschild shows that `ad`-nilpotent elements act nilpotently on modules where the nilradical
does.

## Main results

* `LieIdeal.nilradical_le_restrict_nilradical_of_forall`: if the nilradical of an ideal `I` of a
  Noetherian Lie algebra is stable under every derivation of `I`, it lies in the nilradical of the
  ambient Lie algebra.
* `LieDerivation.apply_mem_nilradical_of_isSolvable`: every derivation of a finite-dimensional
  solvable Lie algebra in characteristic zero takes values in its nilradical.
* `TauCeti.LieAlgebra.lie_radical_le_nilradical`: `⁅L, radical K L⁆ ≤ nilradical K L`.
* `TauCeti.LieAlgebra.mem_nilradical_of_mem_radical_of_isNilpotent_ad`: **the radical
  criterion**, an `ad`-nilpotent element of the radical lies in the nilradical.
* `LieDerivation.apply_mem_nilradical_of_mem_radical`: **every derivation maps the radical into
  the nilradical.**
* `LieDerivation.apply_mem_nilradical_of_mem_nilradical`: the nilradical is stable under every
  derivation.
* `LieIdeal.restrict_nilradical`: the nilradical of an ideal `I` is the nilradical of `L` read
  inside `I`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Appendix E, §E.2,
  the derivation argument in the proof of Proposition E.5.
* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 1-3*][bourbaki1975], Chapter I, §5, for
  the radical and the nilradical under derivations.
* G. Hochschild, *An Addition to Ado's Theorem*, Proc. Amer. Math. Soc. **17** (1966), 531–533,
  for the radical criterion.
-/

public section

open LieAlgebra

namespace TauCeti

open LieAlgebra.SemiDirectSum

section CommRing

variable {R M : Type*} [CommRing R] [LieRing M] [LieAlgebra R M]

/-- If the nilradical of an ideal `I` of a Noetherian Lie algebra `M` is stable under every
derivation of `I`, then it is an ideal of `M`, hence contained in the nilradical of `M`. -/
theorem _root_.LieIdeal.nilradical_le_restrict_nilradical_of_forall [IsNoetherian R M]
    (I : LieIdeal R M)
    (h : ∀ (D : LieDerivation R I I) (z : I), z ∈ LieAlgebra.nilradical R I →
      D z ∈ LieAlgebra.nilradical R I) :
    LieAlgebra.nilradical R I ≤ I.restrict (LieAlgebra.nilradical R M) := by
  -- The nilradical of `I`, as a submodule of `M`, is stable under every `ad x`.
  let N : LieIdeal R M :=
    { toSubmodule := (LieAlgebra.nilradical R I).toSubmodule.map I.incl.toLinearMap
      lie_mem := by
        rintro x _ ⟨z, hz, rfl⟩
        refine ⟨LieIdeal.ad I x z, h _ z hz, ?_⟩
        rw [LieHom.coe_toLinearMap, LieIdeal.incl_apply, LieIdeal.ad_apply_apply]
        exact LieSubmodule.coe_bracket _ x z }
  -- It is the image of the nilpotent Lie algebra `nilradical R I`, so it is nilpotent.
  let f : LieAlgebra.nilradical R I →ₗ⁅R⁆ N :=
    { toFun := fun z ↦ ⟨(z : I), z, z.2, rfl⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      map_lie' := fun {y z} ↦ Subtype.ext <|
        (congrArg _ ((LieAlgebra.nilradical R I : LieSubalgebra R I).coe_bracket y z)).trans <|
          ((I : LieSubalgebra R M).coe_bracket _ _).trans
            ((N : LieSubalgebra R M).coe_bracket (⟨_, y, y.2, rfl⟩ : N) ⟨_, z, z.2, rfl⟩).symm }
  have hf : Function.Surjective f := by
    rintro ⟨_, z, hz, rfl⟩
    exact ⟨⟨z, hz⟩, rfl⟩
  have : LieRing.IsNilpotent N := hf.lieAlgebra_isNilpotent
  exact fun z hz ↦ LieIdeal.mem_restrict.mpr (LieIdeal.le_nilradical R M N this ⟨z, hz, rfl⟩)

end CommRing

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]

-- The field is used as a one-dimensional abelian Lie algebra.
attribute [local instance 100] LieRing.ofAssociativeRing

/-- The derivation `D`, as the Lie homomorphism `a ↦ a • D` out of the one-dimensional abelian
Lie algebra `K`; the semidirect sum it defines adjoins `D` to `L`. -/
private def lineHom (D : LieDerivation K L L) : K →ₗ⁅K⁆ LieDerivation K L L where
  toLinearMap := LinearMap.toSpanSingleton K _ D
  map_lie' := fun {a b} ↦ by simp [Ring.lie_def, mul_comm, smul_lie, lie_smul]

/-- `lineHom D` sends `a` to `a • D`. -/
private theorem lineHom_apply (D : LieDerivation K L L) (a : K) : lineHom D a = a • D :=
  LinearMap.toSpanSingleton_apply K _ D a

/-- In the semidirect sum adjoining `D`, the value `D x` is the bracket of the adjoined
generator with `x`. -/
private theorem lie_inr_one_inl (D : LieDerivation K L L) (x : L) :
    ⁅inr (lineHom D) (1 : K), inl (lineHom D) x⁆ = inl (lineHom D) (D x) := by
  simp only [inl_eq_mk, inr_eq_mk, lie_eq_mk]
  ext <;> simp [lineHom_apply, Ring.lie_def]

/-- If a nilpotent ideal of the semidirect sum adjoining `D` contains the bracket of the adjoined
generator with `x`, then `D x` lies in the nilradical. -/
private theorem apply_mem_nilradical_of_lie_mem (D : LieDerivation K L L) (x : L)
    (J : LieIdeal K (L ⋊⁅lineHom D⁆ K)) [LieRing.IsNilpotent J]
    (hJ : ⁅inr (lineHom D) (1 : K), inl (lineHom D) x⁆ ∈ J) :
    D x ∈ LieAlgebra.nilradical K L := by
  refine LieIdeal.le_nilradical K L (J.comap (inl (lineHom D)))
    (J.isNilpotent_comap_of_injective _ (inl_injective _)) ?_
  rwa [LieIdeal.mem_comap, ← lie_inr_one_inl]

variable [FiniteDimensional K L]

variable [CharZero K]

/-- Every derivation of a finite-dimensional solvable Lie algebra in characteristic zero
takes values in its nilradical. -/
theorem _root_.LieDerivation.apply_mem_nilradical_of_isSolvable [IsSolvable L]
    (D : LieDerivation K L L) (x : L) : D x ∈ LieAlgebra.nilradical K L := by
  have : IsLieAbelian K := isMulCommutative_iff_isLieAbelian.mp inferInstance
  let E := L ⋊⁅lineHom D⁆ K
  have : LieRing.IsNilpotent (derivedSeries K E 1) :=
    (LieIdeal.isNilpotent_iff_isNilpotent_ambient _).mpr
      (isNilpotent_derivedSeries_of_isSolvable (K := K) (L := E) E)
  exact apply_mem_nilradical_of_lie_mem D x (derivedSeries K E 1)
    (LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) (LieSubmodule.mem_top _))

namespace LieAlgebra

variable (K L) in
/-- **The bracket of a Lie algebra with its radical lies in the nilradical**, over a field of
characteristic zero. -/
theorem lie_radical_le_nilradical : ⁅(⊤ : LieIdeal K L), radical K L⁆ ≤ nilradical K L := by
  rw [LieSubmodule.lie_le_iff]
  intro x _ r hr
  have h := LieIdeal.mem_restrict.mp <| (radical K L).nilradical_le_restrict_nilradical_of_forall
    (fun D z _ ↦ D.apply_mem_nilradical_of_isSolvable z)
    ((LieIdeal.ad (radical K L) x).apply_mem_nilradical_of_isSolvable ⟨r, hr⟩)
  rwa [LieIdeal.ad_apply_apply, LieSubmodule.coe_bracket] at h

/-- **The radical criterion**: over a field of characteristic zero, an element of the solvable
radical of a finite-dimensional Lie algebra whose adjoint action is nilpotent lies in the
nilradical. -/
theorem mem_nilradical_of_mem_radical_of_isNilpotent_ad {x : L} (hx : x ∈ radical K L)
    (hnil : IsNilpotent (ad K L x)) : x ∈ nilradical K L := by
  -- `⁅L, radical K L⁆ ≤ nilradical K L` makes `K ∙ x ⊔ nilradical K L` an ideal
  let J : LieIdeal K L :=
    { toSubmodule := (K ∙ x) ⊔ (nilradical K L).toSubmodule
      lie_mem := fun {y m} hm => by
        obtain ⟨a, ha, n, hn, rfl⟩ := Submodule.mem_sup.mp hm
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
        refine Submodule.mem_sup_right ?_
        rw [lie_add, lie_smul]
        exact add_mem (Submodule.smul_mem _ c (lie_radical_le_nilradical K L
          (LieSubmodule.lie_mem_lie (LieSubmodule.mem_top y) hx)))
          ((nilradical K L).lie_mem hn) }
  -- its elements are `ad`-nilpotent, so it is nilpotent by Engel's theorem
  have hJ : LieRing.IsNilpotent J := by
    rw [LieAlgebra.isNilpotent_iff_forall (R := K)]
    intro z
    exact (J : LieSubalgebra K L).isNilpotent_ad_of_isNilpotent_ad (x := z)
      (isNilpotent_ad_of_mem_span_singleton_sup_nilradical hnil z.2)
  exact J.le_nilradical K L hJ (Submodule.mem_sup_left (Submodule.mem_span_singleton_self x))

end LieAlgebra

/-- **Every derivation maps the radical into the nilradical**: for a derivation `D` of a
finite-dimensional Lie algebra over a field of characteristic zero, `D (radical K L)` is contained
in `nilradical K L`. -/
theorem _root_.LieDerivation.apply_mem_nilradical_of_mem_radical (D : LieDerivation K L L)
    {x : L} (hx : x ∈ radical K L) : D x ∈ LieAlgebra.nilradical K L := by
  have : IsLieAbelian K := isMulCommutative_iff_isLieAbelian.mp inferInstance
  let E := L ⋊⁅lineHom D⁆ K
  let π := (radical K E).mkQ
  -- The quotient of `E` by its radical is perfect, by Cartan's criterion.
  have hperf : derivedSeries K (E ⧸ radical K E) 1 = ⊤ :=
    derivedSeries_one_eq_top_of_isKilling K _
  -- The derived algebra of `E` lies in `L`, since `E ⧸ L ≅ K` is abelian.
  have hder (e : E) (he : e ∈ derivedSeries K E 1) : e = inl (lineHom D) e.left := by
    have hle : derivedSeries K E 1 ≤ (projr (lineHom D)).ker := by
      rw [derivedSeries_def, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero,
        LieSubmodule.lie_le_iff]
      intro a _ b _
      simp [LieHom.mem_ker, trivial_lie_zero]
    have hright := hle he
    rw [LieHom.mem_ker, projr_mk] at hright
    ext <;> simp [hright]
  -- Hence `L` surjects onto the quotient of `E` by its radical ...
  have hsurj : Function.Surjective (π.comp (inl (lineHom D))) := by
    intro s
    have hs : s ∈ (derivedSeries K E 1).map π := by
      rw [LieIdeal.derivedSeries_map_eq 1 (radical K E).mkQ_surjective, hperf]
      exact LieSubmodule.mem_top s
    obtain ⟨⟨e, he⟩, rfl⟩ := LieIdeal.mem_map_of_surjective (radical K E).mkQ_surjective hs
    exact ⟨e.left, by rw [LieHom.comp_apply, ← hder e he]⟩
  -- ... which has trivial radical, so the radical of `L` lies in the radical of `E`.
  have hrad : inl (lineHom D) x ∈ radical K E := by
    have hbot : (radical K L).map (π.comp (inl (lineHom D))) = ⊥ :=
      have := LieIdeal.isSolvable_map _ (radical K L) hsurj
      HasTrivialRadical.eq_bot_of_isSolvable _
    have hmem := LieIdeal.mem_map (f := π.comp (inl (lineHom D))) hx
    rw [hbot, LieSubmodule.mem_bot, LieHom.comp_apply, ← LieHom.mem_ker,
      LieIdeal.ker_mkQ] at hmem
    exact hmem
  exact apply_mem_nilradical_of_lie_mem D x (LieAlgebra.nilradical K E)
    (LieAlgebra.lie_radical_le_nilradical K E
      (LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) hrad))

/-- The nilradical of a finite-dimensional Lie algebra over a field of characteristic zero is
stable under every derivation. -/
theorem _root_.LieDerivation.apply_mem_nilradical_of_mem_nilradical (D : LieDerivation K L L)
    {x : L} (hx : x ∈ LieAlgebra.nilradical K L) : D x ∈ LieAlgebra.nilradical K L :=
  D.apply_mem_nilradical_of_mem_radical (LieAlgebra.nilradical_le_radical K L hx)

/-- **The nilradical of an ideal**: over a field of characteristic zero, the nilradical of an
ideal `I` of a finite-dimensional Lie algebra `L` consists of the elements of `I` lying in the
nilradical of `L`. -/
@[simp]
theorem _root_.LieIdeal.restrict_nilradical (I : LieIdeal K L) :
    I.restrict (LieAlgebra.nilradical K L) = LieAlgebra.nilradical K I := by
  refine le_antisymm (fun z hz ↦ ?_) <| I.nilradical_le_restrict_nilradical_of_forall
    fun D _ hz ↦ D.apply_mem_nilradical_of_mem_nilradical hz
  exact LieIdeal.le_nilradical K I _
    ((LieAlgebra.nilradical K L).isNilpotent_comap_of_injective I.incl I.incl_injective)
    (LieIdeal.mem_comap.mpr (LieIdeal.mem_restrict.mp hz))

end TauCeti
