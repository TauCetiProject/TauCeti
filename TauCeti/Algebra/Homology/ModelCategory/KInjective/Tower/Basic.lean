/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.Factorizations.CM5a
public import TauCeti.Algebra.Homology.Embedding.CochainComplex

/-!
# Towers of injective resolutions

Let `C` be an abelian category with enough injectives, and let `⋯ ⟶ T 2 ⟶ T 1 ⟶ T 0` be a
tower of cochain complexes in `C` given by chain maps `u n : T (n + 1) ⟶ T n`, where `T n`
vanishes in degrees below `b n` for an antitone family of bounds `b : ℕ → ℤ`.
This file resolves the whole tower at once: it constructs
monomorphic quasi-isomorphisms `T n ⟶ I n` into complexes of injective objects vanishing below
`b n - 1`, together with transitions `I (n + 1) ⟶ I n` which are degreewise epimorphisms with
injective kernels and commute with the `u n` (`CochainComplex.towerResolution`). Each step is
Mathlib's factorization `CochainComplex.Plus.modelCategoryQuillen.cm5a` of bounded below
complexes, applied to the composite `T (n + 1) ⟶ T n ⟶ I n`.

Applied to the canonical truncations `τ^{≥ -n} K`, this construction gives a resolved truncation
tower and its cone from `K`. The limit results are in
`TauCeti.Algebra.Homology.ModelCategory.KInjective.Tower.Limit`; they use the injective model
structure on unbounded complexes.

## Main declarations

* `CochainComplex.towerResolution`, `CochainComplex.towerResolutionι`,
  `CochainComplex.towerResolutionπ`: the resolution of a tower of bounded below complexes.
* `CochainComplex.truncGETower`, `CochainComplex.truncGETowerCone`: the tower of resolutions of the
  canonical truncations `τ^{≥ -n} K` of a complex `K`, with its cone from `K`.

## References

* N. Spaltenstein, *Resolutions of unbounded complexes*, Compositio Math. 65 (1988), 121–154,
  §3.
* [Stacks: Lemma 13.31.7](https://stacks.math.columbia.edu/tag/070K).
-/

public section

noncomputable section

open CategoryTheory Limits Opposite ZeroObject

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

section TowerResolution

variable [EnoughInjectives C] (b : ℕ → ℤ) (hb : Antitone b)
  (T : ℕ → CochainComplex C ℤ) [∀ n, (T n).IsStrictlyGE (b n)]
  (u : ∀ n, T (n + 1) ⟶ T n)

/-- A level of the resolution of the tower `T`: a monomorphic quasi-isomorphism from `T n` to a
complex of injective objects vanishing below `b n - 1`. -/
private structure TowerLevel (n : ℕ) where
  /-- the resolving complex -/
  obj : CochainComplex C ℤ
  /-- the resolution map -/
  ι : T n ⟶ obj
  mono : Mono ι
  quasiIso : QuasiIso ι
  isStrictlyGE : obj.IsStrictlyGE (b n - 1)
  injective (i : ℤ) : Injective (obj.X i)

/-- The bottom level of the resolution of the tower. -/
private lemma exists_towerLevel_zero : Nonempty (TowerLevel b T 0) := by
  obtain ⟨K, ι, _, _, hinj, _⟩ :=
    Plus.modelCategoryQuillen.exists_mono_quasiIso_injective (T 0) (b 0 - 1) (b 0)
  exact ⟨⟨K, ι, inferInstance, inferInstance, inferInstance, hinj⟩⟩

include hb in
/-- Each level of the resolution of the tower extends to the next one, by a transition which is a
degreewise epimorphism with injective kernels and commutes with the transition of `T`. -/
private lemma exists_towerLevel_succ (n : ℕ) (L : TowerLevel b T n) :
    ∃ (L' : TowerLevel b T (n + 1)) (π : L'.obj ⟶ L.obj),
      degreewiseEpiWithInjectiveKernel π ∧ L'.ι ≫ π = u n ≫ L.ι := by
  have := L.isStrictlyGE
  have : (T (n + 1)).IsStrictlyGE (b (n + 1) - 1 + 1) := by
    simpa using (inferInstance : (T (n + 1)).IsStrictlyGE (b (n + 1)))
  have : L.obj.IsStrictlyGE (b (n + 1) - 1) :=
    L.obj.isStrictlyGE_of_ge _ (b n - 1) (by have := hb (Nat.le_succ n); lia)
  obtain ⟨K, _, ι, π, _, _, hπ, fac⟩ :=
    Plus.modelCategoryQuillen.cm5a (u n ≫ L.ι) (b (n + 1) - 1)
  have := L.injective
  have hinj := (degreewiseEpiWithInjectiveKernel_iff_of_isZero (π ≫ (0 : L.obj ⟶ 0))
    (isZero_zero _)).1 (MorphismProperty.comp_mem _ _ _ hπ
      ((degreewiseEpiWithInjectiveKernel_iff_of_isZero _ (isZero_zero _)).2 L.injective))
  exact ⟨⟨K, ι, inferInstance, inferInstance, inferInstance, hinj⟩, π, hπ, fac⟩

/-- The levels of the resolution of the tower `T`, chosen inductively. -/
private def towerLevel : (n : ℕ) → TowerLevel b T n
  | 0 => (exists_towerLevel_zero b T).some
  | n + 1 => (exists_towerLevel_succ b hb T u n (towerLevel n)).choose

/-- The `n`-th complex of the resolution of the tower `T`: a complex of injective objects vanishing
below `b n - 1`, with a monomorphic quasi-isomorphism `CochainComplex.towerResolutionι` from `T n`.
-/
def towerResolution (n : ℕ) : CochainComplex C ℤ := (towerLevel b hb T u n).obj

/-- The monomorphic quasi-isomorphism `T n ⟶ I n` of the resolution of the tower `T`. -/
def towerResolutionι (n : ℕ) : T n ⟶ towerResolution b hb T u n := (towerLevel b hb T u n).ι

/-- The transition `I (n + 1) ⟶ I n` of the resolution of the tower `T`, a degreewise epimorphism
with injective kernels. -/
def towerResolutionπ (n : ℕ) : towerResolution b hb T u (n + 1) ⟶ towerResolution b hb T u n :=
  (exists_towerLevel_succ b hb T u n (towerLevel b hb T u n)).choose_spec.choose

instance (n : ℕ) : Mono (towerResolutionι b hb T u n) := (towerLevel b hb T u n).mono

instance (n : ℕ) : QuasiIso (towerResolutionι b hb T u n) := (towerLevel b hb T u n).quasiIso

instance (n : ℕ) : (towerResolution b hb T u n).IsStrictlyGE (b n - 1) :=
  (towerLevel b hb T u n).isStrictlyGE

instance (n : ℕ) (i : ℤ) : Injective ((towerResolution b hb T u n).X i) :=
  (towerLevel b hb T u n).injective i

instance (n : ℕ) : (towerResolution b hb T u n).IsKInjective :=
  isKInjective_of_injective _ (b n - 1)

lemma degreewiseEpiWithInjectiveKernel_towerResolutionπ (n : ℕ) :
    degreewiseEpiWithInjectiveKernel (towerResolutionπ b hb T u n) :=
  (exists_towerLevel_succ b hb T u n (towerLevel b hb T u n)).choose_spec.choose_spec.1

/-- The transitions of the resolution of the tower `T` are degreewise split epimorphisms. -/
instance isSplitEpi_towerResolutionπ_f (n : ℕ) (i : ℤ) :
    IsSplitEpi ((towerResolutionπ b hb T u n).f i) :=
  have ⟨_, _, _, _, ⟨σ⟩⟩ := (Abelian.epiWithInjectiveKernel_iff _).1
    (degreewiseEpiWithInjectiveKernel_towerResolutionπ b hb T u n i)
  ⟨σ.s, σ.s_g⟩

/-- The resolutions commute with the transitions: `ι (n + 1) ≫ π n = u n ≫ ι n`. -/
@[reassoc]
lemma towerResolutionι_comp_towerResolutionπ (n : ℕ) :
    towerResolutionι b hb T u (n + 1) ≫ towerResolutionπ b hb T u n =
      u n ≫ towerResolutionι b hb T u n :=
  (exists_towerLevel_succ b hb T u n (towerLevel b hb T u n)).choose_spec.choose_spec.2

end TowerResolution

section TruncGETower

variable [EnoughInjectives C] (K : CochainComplex C ℤ)

/-- The tower `⋯ ⟶ I₁ ⟶ I₀` of injective resolutions of the canonical truncations `τ^{≥ -n} K` of a
complex `K`, obtained by resolving the tower of truncations with `CochainComplex.towerResolution`.
Its transitions are degreewise split epimorphisms with injective kernels. -/
abbrev truncGETower : ℕᵒᵖ ⥤ CochainComplex C ℤ :=
  Functor.ofOpSequence (towerResolutionπ (fun n : ℕ ↦ -(n : ℤ)) Nat.mono_cast.neg
      (fun n ↦ K.truncGE (-(n : ℤ)))
    (fun n ↦ K.truncGETransition (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by lia)))

/-- The resolution quasi-isomorphism from the `n`-th truncation to its tower level. -/
def truncGETowerResolutionι (n : ℕ) : K.truncGE (-(n : ℤ)) ⟶ (truncGETower K).obj (op n) :=
  towerResolutionι (fun n : ℕ ↦ -(n : ℤ)) Nat.mono_cast.neg
    (fun n ↦ K.truncGE (-(n : ℤ)))
    (fun n ↦ K.truncGETransition (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by lia)) n

instance (n : ℕ) : Mono (K.truncGETowerResolutionι n) :=
  inferInstanceAs (Mono (towerResolutionι _ _ _ _ n))

instance (n : ℕ) : QuasiIso (K.truncGETowerResolutionι n) :=
  inferInstanceAs (QuasiIso (towerResolutionι _ _ _ _ n))

instance (n : ℕ) : ((truncGETower K).obj (op n)).IsStrictlyGE (-(n : ℤ) - 1) :=
  inferInstanceAs ((towerResolution _ _ _ _ n).IsStrictlyGE (-(n : ℤ) - 1))

instance (n : ℕ) (i : ℤ) : Injective (((truncGETower K).obj (op n)).X i) :=
  inferInstanceAs (Injective ((towerResolution _ _ _ _ n).X i))

instance (n : ℕ) : ((truncGETower K).obj (op n)).IsKInjective :=
  isKInjective_of_injective _ (-(n : ℤ) - 1)

/-- The map `K ⟶ Iₙ` from `K` to the `n`-th term of `CochainComplex.truncGETower K`: the
truncation `K ⟶ τ^{≥ -n} K` followed by the resolution of `τ^{≥ -n} K`. -/
def truncGETowerι (n : ℕ) : K ⟶ (truncGETower K).obj (op n) :=
  K.πTruncGE (-(n : ℤ)) ≫ K.truncGETowerResolutionι n

/-- The tower leg factors through the canonical truncation and its injective resolution. -/
lemma truncGETowerι_eq (n : ℕ) :
    K.truncGETowerι n = K.πTruncGE (-(n : ℤ)) ≫ K.truncGETowerResolutionι n := (rfl)

/-- The resolutions of successive truncations commute with the tower transition. -/
@[reassoc]
lemma truncGETowerResolutionι_comp_map (n : ℕ) :
    K.truncGETowerResolutionι (n + 1) ≫
        (truncGETower K).map (homOfLE (Nat.le_succ n)).op =
      K.truncGETransition (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by lia) ≫
        K.truncGETowerResolutionι n := by
  rw [Functor.ofOpSequence_map_homOfLE_succ]
  exact towerResolutionι_comp_towerResolutionπ _ _ _ _ n

/-- The maps `K ⟶ Iₙ` are compatible with the transitions of `CochainComplex.truncGETower K`. -/
@[reassoc]
lemma truncGETowerι_comp_map (n : ℕ) :
    K.truncGETowerι (n + 1) ≫ (truncGETower K).map (homOfLE (Nat.le_succ n)).op =
      K.truncGETowerι n := by
  rw [truncGETowerι_eq, truncGETowerι_eq, Category.assoc,
    truncGETowerResolutionι_comp_map, πTruncGE_truncGETransition_assoc]

/-- The cone over `CochainComplex.truncGETower K` with point `K`, given by the maps
`CochainComplex.truncGETowerι`. -/
-- Consumers use the cone as a cone with point K, so its point must compute across modules.
@[expose]
def truncGETowerCone : Cone (truncGETower K) :=
  Cone.mk K <| NatTrans.ofOpSequence K.truncGETowerι
    (fun n ↦ (Category.id_comp _).trans (K.truncGETowerι_comp_map n).symm)

@[simp]
lemma truncGETowerCone_pt : (truncGETowerCone K).pt = K := (rfl)

@[simp]
lemma truncGETowerCone_π_app (n : ℕ) : (truncGETowerCone K).π.app (op n) = K.truncGETowerι n :=
  (rfl)

/-- The map `K ⟶ Iₙ` induces isomorphisms on cohomology in degrees `≥ -n`. -/
lemma quasiIsoAt_truncGETowerι (n : ℕ) (j : ℤ) (hj : -(n : ℤ) ≤ j) :
    QuasiIsoAt (K.truncGETowerι n) j :=
  have := K.quasiIsoAt_πTruncGE _ j hj
  quasiIsoAt_comp _ (K.truncGETowerResolutionι n) j

/-- The transitions of `CochainComplex.truncGETower K` induce isomorphisms on cohomology in degrees
`≥ -n`. -/
lemma quasiIsoAt_truncGETower_map (n : ℕ) (j : ℤ) (hj : -(n : ℤ) ≤ j) :
    QuasiIsoAt ((truncGETower K).map (homOfLE (Nat.le_succ n)).op) j := by
  have := K.quasiIsoAt_truncGETowerι (n + 1) j (by push_cast; lia)
  refine quasiIsoAt_of_comp_left (K.truncGETowerι (n + 1)) _ j (hφφ' := ?_)
  rw [truncGETowerι_comp_map]
  exact K.quasiIsoAt_truncGETowerι n j hj

/-- The transitions of `CochainComplex.truncGETower K` are degreewise split epimorphisms. -/
lemma isSplitEpi_truncGETower_map_f (n : ℕ) (i : ℤ) :
    IsSplitEpi (((truncGETower K).map (homOfLE (Nat.le_succ n)).op).f i) := by
  rw [Functor.ofOpSequence_map_homOfLE_succ]
  exact isSplitEpi_towerResolutionπ_f _ _ _ _ n i

end TruncGETower

end CochainComplex
