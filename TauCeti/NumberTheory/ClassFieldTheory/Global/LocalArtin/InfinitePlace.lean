/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.DecompositionRestrict
public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Archimedean.ArtinMap
public import TauCeti.NumberTheory.NumberField.ComplexConjugation.Basic
public import TauCeti.NumberTheory.NumberField.InfinitePlace.Completion.DecompositionGroup
import TauCeti.NumberTheory.NumberField.InfinitePlace.Completion.Norm
import TauCeti.RingTheory.Norm.Equiv

/-!
# The local Artin symbols at the infinite places in a finite Galois extension

Let `L/K` be a finite normal extension of fields and `v` an infinite place of `K`, with
completion `K_v`, which is `ℝ` or `ℂ`. The archimedean Artin map
`infiniteArtinAt v : K_vˣ → G_{K_v}^ab`, read in `Gal(L/K)^ab` by restricting along a place of `L`
above `v` (`TauCeti.decompositionRestrict`), is the **local Artin symbol at `v`**

```text
infiniteLocalArtinAt K L v : K_vˣ →* Gal(L/K)^ab.
```

In global class field theory it is the local factor at `v` of the global Artin map. It is a
reading of `infiniteArtinAt`, not a second archimedean Artin map, and it is compatible with
restriction to a normal subextension (`infiniteLocalArtinAt_comp`).

For a place `w` of `L` above `v` the symbol is explicit, through the decomposition group of `w`,
which acts on `L_w` (`NumberField.InfinitePlace.decompositionHom`).

* If `w` is unramified over `K`, then `L_w = K_v` and the symbol is trivial
  (`infiniteLocalArtinAt_eq_one_of_isUnramified`); in particular at a complex place of `K`
  (`infiniteLocalArtinAt_eq_one_of_isComplex`).
* At a real place `v` the symbol of a positive element is trivial
  (`infiniteLocalArtinAt_eq_one_of_pos`). If `L/K` is Galois and `w` is ramified over `K`, so that
  `w` is complex and its decomposition group has order two, the symbol of a negative element is
  the class of the nontrivial element of that group, the complex conjugation at `w`
  (`TauCeti.NumberField.complexConjugationAt`, `infiniteLocalArtinAt_eq_complexConjugationAt`).

Consequently, for `L/K` Galois, the image of the symbol is the image of the decomposition group
of `w` (`range_infiniteLocalArtinAt`), the local norms `N_{L_w/K_v}(L_wˣ)` lie in its kernel
(`normGroup_le_ker_infiniteLocalArtinAt`), and for `L/K` abelian they are exactly its kernel
(`infiniteLocalArtinAt_eq_one_iff_mem_normGroup`): the archimedean form of local reciprocity
`K_vˣ / N_{L_w/K_v}(L_wˣ) ≃ Gal(L_w/K_v)`.

## Main definitions

* `TauCeti.ClassFieldTheory.infiniteLocalArtinAt K L v`: the local Artin symbol at the infinite
  place `v`, with values in `Gal(L/K)^ab`.

## Main results

* `TauCeti.ClassFieldTheory.infiniteLocalArtinAt_eq_of_decompositionHom`: the symbol of `x` is the
  class of the element of the decomposition group of `w` acting on `L_w` as a representative of the
  archimedean Artin symbol of `x`.
* `TauCeti.ClassFieldTheory.infiniteLocalArtinAt_eq_one_of_isUnramified`: the symbol is trivial at
  a place unramified in `L`.
* `TauCeti.ClassFieldTheory.infiniteLocalArtinAt_eq_complexConjugationAt`: at a complex place `w`
  over a real place, a negative element has as symbol the class of complex conjugation at `w`.
* `TauCeti.ClassFieldTheory.range_infiniteLocalArtinAt`: the image of the symbol is the image of
  the decomposition group.
* `TauCeti.ClassFieldTheory.normGroup_le_ker_infiniteLocalArtinAt`,
  `TauCeti.ClassFieldTheory.infiniteLocalArtinAt_eq_one_iff_mem_normGroup`: local norms have trivial
  symbol, and for `L/K` abelian exactly the local norms do.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, §8 (infinite places and their decomposition
  groups) and Chapter VI, §5 (the global reciprocity law and its local factors).
* J. S. Milne, *Class Field Theory*, Chapter VII, §8 (the local Artin symbol at an archimedean
  place).
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open _root_.NumberField _root_.NumberField.InfinitePlace
open scoped _root_.NumberField.LiesOver

variable (K : Type) [Field K] (L : Type) [Field L] [Algebra K L]

/-! ### The local Artin symbol -/

section Normal

variable [FiniteDimensional K L] [Normal K L]

/-- **The local Artin symbol at an infinite place** `v` of `K`, with values in the abelianized
Galois group of a finite normal extension `L/K`: the archimedean Artin map of the completion `K_v`,
read in `Gal(L/K)^ab` by restriction along a place of `L` above `v`
(`TauCeti.decompositionRestrict`). It does not depend on the choice of that place. -/
def infiniteLocalArtinAt (v : InfinitePlace K) :
    v.Completionˣ →* Abelianization Gal(L/K) :=
  (decompositionRestrict K v.Completion L).comp (infiniteArtinAt v)

variable {K L}

/-- The local Artin symbol at `v` is the archimedean Artin map of `K_v` followed by restriction to
`L`. -/
theorem infiniteLocalArtinAt_apply (v : InfinitePlace K) (x : v.Completionˣ) :
    infiniteLocalArtinAt K L v x =
      decompositionRestrict K v.Completion L (infiniteArtinAt v x) :=
  (rfl)

/-- **The local Artin symbol through a representative.** If `τ ∈ G_{K_v}` represents the
archimedean Artin symbol of `x`, then for every `K`-embedding `j : L → K_vᵃˡᵍ` the local Artin
symbol of `x` at `v` is the class of the automorphism `σ` of `L` with `j ∘ σ = τ ∘ j`. -/
theorem infiniteLocalArtinAt_eq_of_mk_eq_infiniteArtinAt (v : InfinitePlace K)
    {x : v.Completionˣ} (τ : Field.absoluteGaloisGroup v.Completion)
    (hτ : (τ : Field.absoluteGaloisGroupAbelianization v.Completion) = infiniteArtinAt v x)
    (j : L →ₐ[K] AlgebraicClosure v.Completion) (σ : Gal(L/K))
    (hσ : ∀ y : L, j (σ y) = τ.toRingEquiv (j y)) :
    infiniteLocalArtinAt K L v x = Abelianization.of σ := by
  rw [infiniteLocalArtinAt_apply, ← hτ, decompositionRestrict_mk j τ σ hσ]

/-- **Compatibility with restriction to a normal subextension.** For a `K`-embedding
`f : M → L` of a finite normal extension `M/K`, the local Artin symbol at `v` in `Gal(L/K)^ab`,
restricted to `M` along `f`, is the local Artin symbol at `v` in `Gal(M/K)^ab`. -/
theorem infiniteLocalArtinAt_comp (v : InfinitePlace K) {M : Type} [Field M] [Algebra K M]
    [FiniteDimensional K M] [Normal K M] (f : M →ₐ[K] L) :
    (Abelianization.map f.restrictNormalHom).comp (infiniteLocalArtinAt K L v) =
      infiniteLocalArtinAt K M v := by
  rw [infiniteLocalArtinAt, infiniteLocalArtinAt, ← MonoidHom.comp_assoc,
    decompositionRestrict_comp]

/-- **The local Artin symbol at a complex place is trivial**: the absolute Galois group of
`K_v ≅ ℂ` is trivial. -/
@[simp]
theorem infiniteLocalArtinAt_eq_one_of_isComplex {v : InfinitePlace K} (hv : v.IsComplex)
    (x : v.Completionˣ) : infiniteLocalArtinAt K L v x = 1 := by
  rw [infiniteLocalArtinAt_apply, infiniteArtinAt_eq_one_of_isComplex v hv, map_one]

/-- **Positive elements have trivial local Artin symbol** at a real place: they lie in the kernel
of the real Artin map. -/
theorem infiniteLocalArtinAt_eq_one_of_pos {v : InfinitePlace K} (hv : v.IsReal)
    {x : v.Completionˣ} (hx : 0 < Completion.extensionEmbeddingOfIsReal hv (x : v.Completion)) :
    infiniteLocalArtinAt K L v x = 1 := by
  rw [infiniteLocalArtinAt_apply, (infiniteArtinAt_eq_one_iff_of_isReal v hv x).2 hx, map_one]

end Normal

/-! ### The local Artin symbol through the decomposition group -/

section Place

variable {K L} [FiniteDimensional K L] [Normal K L]
  (v : InfinitePlace K) (w : InfinitePlace L) [w.LiesOver v]

/-- **The local Artin symbol through the decomposition group.** Let `w` be a place of `L` above
`v`, `ι : L_w → K_vᵃˡᵍ` a `K_v`-embedding and `τ ∈ G_{K_v}` a representative of the archimedean
Artin symbol of `x`. If `σ` is in the decomposition group of `w` and acts on `L_w` as `τ` does
through `ι`, then the local Artin symbol of `x` at `v` is the class of `σ`. -/
theorem infiniteLocalArtinAt_eq_of_decompositionHom {x : v.Completionˣ}
    (τ : Field.absoluteGaloisGroup v.Completion)
    (hτ : (τ : Field.absoluteGaloisGroupAbelianization v.Completion) = infiniteArtinAt v x)
    (ι : w.Completion →ₐ[v.Completion] AlgebraicClosure v.Completion)
    (σ : MulAction.stabilizer Gal(L/K) w)
    (hσ : ∀ y, ι (decompositionHom v w σ y) = τ.toRingEquiv (ι y)) :
    infiniteLocalArtinAt K L v x = Abelianization.of (σ : Gal(L/K)) := by
  refine infiniteLocalArtinAt_eq_of_mk_eq_infiniteArtinAt v τ hτ
    ((ι.restrictScalars K).comp (IsScalarTower.toAlgHom K L w.Completion)) σ fun y ↦ ?_
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, IsScalarTower.coe_toAlgHom',
    Completion.algebraMap_apply]
  rw [← decompositionHom_algebraMap (v := v) σ y, hσ]

include w in
/-- **The local Artin symbol at an unramified place is trivial.** If a place `w` of `L` above `v`
is unramified over `K`, then `L_w = K_v`, and every element of `G_{K_v}` acts trivially on it. -/
theorem infiniteLocalArtinAt_eq_one_of_isUnramified (hw : w.IsUnramified K)
    (x : v.Completionˣ) : infiniteLocalArtinAt K L v x = 1 := by
  obtain ⟨τ, hτ⟩ := QuotientGroup.mk_surjective (infiniteArtinAt v x)
  rw [infiniteLocalArtinAt_eq_of_decompositionHom v w τ hτ IsAlgClosed.lift 1 fun y ↦ ?_,
    OneMemClass.coe_one, map_one]
  -- `L_w` has degree one over `K_v`, so `y` comes from `K_v`, which `τ` fixes
  obtain ⟨a, rfl⟩ :=
    (Module.Free.bijective_algebraMap_of_finrank_eq_one (hw.finrank_eq_one v)).2 y
  rw [map_one, AlgEquiv.one_apply, AlgHom.commutes]
  exact (τ.commutes a).symm

include w in
/-- **Local norms have trivial local Artin symbol.** For a place `w` of `L` above `v`, the norms
from `L_w` lie in the kernel of the local Artin symbol at `v`: at an unramified place it is
trivial, and at a complex place over a real place the norms are the positive elements. -/
theorem normGroup_le_ker_infiniteLocalArtinAt :
    TauCeti.normGroup v.Completion w.Completion ≤ (infiniteLocalArtinAt K L v).ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  rcases w.isUnramified_or_isRamified K with h | h
  · exact infiniteLocalArtinAt_eq_one_of_isUnramified v w h x
  · have hv : v.IsReal := h.liesOver_isReal_under w v
    exact infiniteLocalArtinAt_eq_one_of_pos hv
      ((Completion.mem_normGroup_iff_of_isRamified h hv).1 hx)

section IsGalois

variable [IsGalois K L]

/-- **The local Artin symbol of a negative element is complex conjugation.** Let `L/K` be Galois
and `w` a place of `L` ramified over `K`, so that `w` is complex and the place `v` below it is
real. Every `x ∈ K_vˣ` that is negative in `K_v ≅ ℝ` has as local Artin symbol the class of the
complex conjugation at `w`, the nontrivial element of its decomposition group. -/
theorem infiniteLocalArtinAt_eq_complexConjugationAt (hw : w.IsRamified K) {x : v.Completionˣ}
    (hx : Completion.extensionEmbeddingOfIsReal (hw.liesOver_isReal_under w v)
      (x : v.Completion) < 0) :
    infiniteLocalArtinAt K L v x =
      Abelianization.of (NumberField.complexConjugationAt K w hw) := by
  have hv : v.IsReal := hw.liesOver_isReal_under w v
  obtain ⟨τ, hτ⟩ := QuotientGroup.mk_surjective (infiniteArtinAt v x)
  have hτ1 : τ ≠ 1 := by
    rintro rfl
    rw [QuotientGroup.mk_one, eq_comm, infiniteArtinAt_eq_one_iff_of_isReal v hv] at hτ
    exact hτ.not_gt hx
  -- `L_w ≅ ℂ` is algebraically closed, so it is all of the algebraic closure of `K_v ≅ ℝ`
  have : IsAlgClosed w.Completion :=
    IsAlgClosed.of_ringEquiv ℂ w.Completion
      (Completion.ringEquivComplexOfIsComplex hw.isComplex).symm
  obtain ⟨ι⟩ : Nonempty (w.Completion →ₐ[v.Completion] AlgebraicClosure v.Completion) :=
    ⟨IsAlgClosed.lift⟩
  have hint : (ι : w.Completion →+* AlgebraicClosure v.Completion).IsIntegral := by
    refine RingHom.IsIntegral.tower_top (algebraMap v.Completion w.Completion) _ ?_
    rw [ι.comp_algebraMap]
    exact fun z ↦ Algebra.IsIntegral.isIntegral z
  have hι : Function.Bijective ι := IsAlgClosed.ringHom_bijective_of_isIntegral _ hint
  let e : w.Completion ≃ₐ[v.Completion] AlgebraicClosure v.Completion := AlgEquiv.ofBijective ι hι
  -- the automorphism `ρ` of `L_w` induced by `τ`, and an element `σ'` of the decomposition
  -- group inducing it; `Field.absoluteGaloisGroup F` is by definition the group
  -- `AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F`
  let τ' : AlgebraicClosure v.Completion ≃ₐ[v.Completion] AlgebraicClosure v.Completion := τ
  let ρ : w.Completion ≃ₐ[v.Completion] w.Completion := (e.trans τ').trans e.symm
  obtain ⟨σ', hσ'⟩ := decompositionHom_surjective v w ρ
  have hρ (y : w.Completion) : ι (ρ y) = τ.toRingEquiv (ι y) :=
    e.apply_symm_apply (τ' (e y))
  rw [infiniteLocalArtinAt_eq_of_decompositionHom v w τ hτ ι σ' fun y ↦ by rw [hσ', hρ]]
  -- `σ'` is not trivial, since `τ` is not, so it is the complex conjugation at `w`
  have hσ'1 : σ' ≠ 1 := by
    rintro rfl
    refine hτ1 (AlgEquiv.ext fun z ↦ ?_)
    have h := congr(e ($hσ' (e.symm z)))
    rw [map_one, AlgEquiv.one_apply, AlgEquiv.apply_symm_apply] at h
    simp only [ρ, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply] at h
    -- `τ'` is `τ`, read as an automorphism of the algebraic closure
    exact h.symm
  rw [NumberField.eq_complexConjugationAt_of_mem_stabilizer_of_ne_one K w hw σ'.2
    fun h ↦ hσ'1 (Subtype.ext h)]

/-- **The image of the local Artin symbol is the decomposition group.** For `L/K` Galois and `w` a
place of `L` above `v`, the local Artin symbols at `v` are exactly the classes in `Gal(L/K)^ab` of
the elements of the decomposition group of `w`. -/
theorem range_infiniteLocalArtinAt :
    (infiniteLocalArtinAt K L v).range =
      (MulAction.stabilizer Gal(L/K) w).map Abelianization.of := by
  rcases w.isUnramified_or_isRamified K with h | h
  · rw [h.stabilizer_eq_bot, Subgroup.map_bot, eq_bot_iff]
    rintro _ ⟨x, rfl⟩
    exact infiniteLocalArtinAt_eq_one_of_isUnramified v w h x
  have hv : v.IsReal := h.liesOver_isReal_under w v
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    rcases ((map_ne_zero (Completion.extensionEmbeddingOfIsReal hv)).2 x.ne_zero).lt_or_gt
      with hneg | hpos
    · exact ⟨_, NumberField.complexConjugationAt_mem_stabilizer K w h,
        (infiniteLocalArtinAt_eq_complexConjugationAt v w h hneg).symm⟩
    · rw [infiniteLocalArtinAt_eq_one_of_pos hv hpos]
      exact one_mem _
  · rintro _ ⟨σ, hσ, rfl⟩
    rcases eq_or_ne σ 1 with rfl | hσ1
    · rw [map_one]
      exact one_mem _
    · rw [NumberField.eq_complexConjugationAt_of_mem_stabilizer_of_ne_one K w h hσ hσ1]
      refine ⟨-1, infiniteLocalArtinAt_eq_complexConjugationAt v w h ?_⟩
      simp

/-- **For an abelian extension, the kernel of the local Artin symbol is the local norm group.**
If `Gal(L/K)` is commutative and `w` is a place of `L` above `v`, then `x ∈ K_vˣ` has trivial
local Artin symbol at `v` exactly when it is a norm from `L_w`. -/
theorem infiniteLocalArtinAt_eq_one_iff_mem_normGroup [IsMulCommutative Gal(L/K)]
    (x : v.Completionˣ) :
    infiniteLocalArtinAt K L v x = 1 ↔ x ∈ TauCeti.normGroup v.Completion w.Completion := by
  refine ⟨fun h1 ↦ ?_, fun hx ↦ normGroup_le_ker_infiniteLocalArtinAt v w hx⟩
  rcases w.isUnramified_or_isRamified K with h | h
  · rw [normGroup_eq_top_of_finrank_eq_one (h.finrank_eq_one v)]
    exact Subgroup.mem_top x
  have hv : v.IsReal := h.liesOver_isReal_under w v
  rw [Completion.mem_normGroup_iff_of_isRamified h hv]
  by_contra hx
  have hneg : Completion.extensionEmbeddingOfIsReal hv (x : v.Completion) < 0 :=
    (not_lt.1 hx).lt_of_ne ((map_ne_zero _).2 x.ne_zero)
  rw [infiniteLocalArtinAt_eq_complexConjugationAt v w h hneg] at h1
  -- `Gal(L/K)` is commutative, so it embeds in its abelianization
  have hker : (Abelianization.of (G := Gal(L/K))).ker = ⊥ := by
    rw [Abelianization.ker_of, commutator_eq_bot]
  exact NumberField.complexConjugationAt_ne_one K w h
    ((Subgroup.mem_bot).1 (hker ▸ (MonoidHom.mem_ker.2 h1)))

end IsGalois

end Place

end TauCeti.ClassFieldTheory
