/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.Unramified
public import TauCeti.NumberTheory.ClassFieldTheory.WeilGroup.Abelianization
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular
import TauCeti.NumberTheory.LocalField.UnitsDecomposition
import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Decomposition

/-!
# The image of the local Artin map and the Artin map into the Weil group

Let `K` be a nonarchimedean local field. The absolute local Artin map `artinMap K : Kˣ →* G_K^ab`
has dense image, but it is not surjective. This file identifies its image: it is the subgroup
`integralUnramifiedSubgroup K` of classes whose unramified coordinate in `ℤ̂` is an integer
(`range_artinMap`), which is also the image of the abelianized Weil group `W_K^ab → G_K^ab`
(`range_weilToAbsoluteAbelianization`). So a class in `G_K^ab` is an Artin symbol exactly when it
is the class of an element of the Weil group (`mem_range_artinMap_iff`).

Since `W_K^ab → G_K^ab` is injective, the Artin map therefore factors uniquely through `W_K^ab`,
as `weilArtinMap K : Kˣ →* W_K^ab`. Unlike `artinMap K`, it is surjective, and it is a quotient
map of topological groups: it is continuous, because the topology of `W_K^ab` is the one induced
by `x ↦ (x, deg x)` into `G_K^ab × ℤ` and the degree of `weilArtinMap K x` is the normalized
valuation of `x`, and it is open by the open mapping theorem, since `Kˣ` is σ-compact and `W_K^ab`
is locally compact. Its kernel is that of `artinMap K`.

The inclusion of the image in `integralUnramifiedSubgroup K` is the computation of the unramified
coordinate of an Artin symbol as the normalized valuation (`unramifiedCoordinate_artinMap`). For
the reverse inclusion, a class with unramified coordinate `n ∈ ℤ` differs from the Artin symbol of
an element of valuation `n` by a class with trivial coordinate, that is, by the image of an
element of inertia, and these are the Artin symbols of the units of `𝒪[K]`
(`map_artinMap_unitFiltration_zero`).

None of this needs local existence, so it holds for every nonarchimedean local field, in every
characteristic.

## Main results

* `TauCeti.ClassFieldTheory.range_artinMap`: the image of the absolute local Artin map is the
  subgroup of classes with integral unramified coordinate.
* `TauCeti.ClassFieldTheory.mem_range_artinMap_iff`: a class in `G_K^ab` is an Artin symbol exactly
  when it is the class of an element of the Weil group.
* `TauCeti.ClassFieldTheory.not_surjective_artinMap`: the absolute local Artin map is not
  surjective.
* `TauCeti.ClassFieldTheory.weilArtinMap`: the local Artin map `Kˣ →* W_K^ab`, characterized by
  `weilToAbsoluteAbelianization_weilArtinMap` and `weilDegreeAbelianization_weilArtinMap`.
* `TauCeti.ClassFieldTheory.continuous_weilArtinMap`,
  `TauCeti.ClassFieldTheory.isOpenMap_weilArtinMap`,
  `TauCeti.ClassFieldTheory.surjective_weilArtinMap` and
  `TauCeti.ClassFieldTheory.ker_weilArtinMap`: it is a continuous open surjection with the same
  kernel as `artinMap K`.

## References

* J. Tate, *Number theoretic background*, in *Automorphic forms, representations and
  L-functions*, Proc. Sympos. Pure Math. 33, Part 2 (1979), §1.4.
* J.-P. Serre, *Local class field theory*, in J. W. S. Cassels and A. Fröhlich (eds.),
  *Algebraic Number Theory*, Chapter VI, §2.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- **The image of the absolute local Artin map** consists exactly of the classes in `G_K^ab`
whose unramified coordinate is an integer. -/
theorem range_artinMap : (artinMap K).range = integralUnramifiedSubgroup K := by
  ext y
  rw [mem_integralUnramifiedSubgroup_iff]
  refine ⟨?_, fun ⟨n, hn⟩ ↦ ?_⟩
  · rintro ⟨x, rfl⟩
    exact ⟨normalizedValuation K x, (unramifiedCoordinate_artinMap K x).symm⟩
  · -- `y` differs from the Artin symbol of an element `x` of valuation `n` by a class with
    -- trivial unramified coordinate, which is the Artin symbol of a unit.
    obtain ⟨x, hx⟩ := normalizedValuation_surjective (K := K) n
    have hy : y * (artinMap K x)⁻¹ ∈ (unramifiedCoordinate K).toMonoidHom.ker := by
      have hn' : unramifiedCoordinate K y = zHat.ofInt n := hn.symm
      simp [MonoidHom.mem_ker, hx, hn']
    rw [ker_unramifiedCoordinate, ← map_artinMap_unitFiltration_zero] at hy
    obtain ⟨u, -, hu⟩ := hy
    exact ⟨u * x, by rw [map_mul, hu, inv_mul_cancel_right]⟩

/-- **The Artin symbols are the classes of the Weil group.** A class in `G_K^ab` is the Artin
symbol of an element of `Kˣ` exactly when it is the class of an element of the local Weil group
`W_K`. -/
theorem mem_range_artinMap_iff (y : Field.absoluteGaloisGroupAbelianization K) :
    y ∈ (artinMap K).range ↔
      ∃ w : WeilGroup K,
        (QuotientGroup.mk (weilToAbsolute K w) :
          Field.absoluteGaloisGroupAbelianization K) = y := by
  rw [range_artinMap, ← range_weilToAbsoluteAbelianization]
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective w
    exact ⟨w, (weilToAbsoluteAbelianization_mk K w).symm⟩
  · rintro ⟨w, rfl⟩
    exact ⟨w, weilToAbsoluteAbelianization_mk K w⟩

/-- **The absolute local Artin map is not surjective**: the unramified coordinate of an Artin
symbol is an integer, while the unramified coordinate takes every value in `ℤ̂ ≠ ℤ`. -/
theorem not_surjective_artinMap : ¬ Function.Surjective (artinMap K) := fun h ↦
  zHat.not_surjective_ofInt fun z ↦ by
    obtain ⟨y, rfl⟩ := unramifiedCoordinate_surjective K z
    exact (mem_integralUnramifiedSubgroup_iff K y).1 <|
      range_artinMap K ▸ (artinMap K).mem_range.2 (h y)

/-! ### The Artin map into the abelianized Weil group -/

/-- **The local Artin map into the abelianized Weil group**, `Kˣ →* W_K^ab`: the lift of the
absolute local Artin map `artinMap K` along the injection `W_K^ab → G_K^ab`
(`weilToAbsoluteAbelianization_weilArtinMap`), which exists because both maps have the same image
(`range_artinMap`, `range_weilToAbsoluteAbelianization`). It is surjective
(`surjective_weilArtinMap`), and in characteristic zero it is an isomorphism of topological groups
(`localWeilArtinEquiv`). -/
def weilArtinMap : Kˣ →* TopologicalAbelianization (WeilGroup K) :=
  (weilAbelianizationEquivIntegralUnramified K).symm.toMonoidHom.comp <|
    (artinMap K).codRestrict _ fun x ↦ range_artinMap K ▸ ⟨x, rfl⟩

/-- The image of `weilArtinMap K x` in `G_K^ab` is the Artin symbol of `x`. Since
`W_K^ab → G_K^ab` is injective, this determines `weilArtinMap K`. -/
@[simp]
theorem weilToAbsoluteAbelianization_weilArtinMap (x : Kˣ) :
    weilToAbsoluteAbelianization K (weilArtinMap K x) = artinMap K x :=
  weilToAbsoluteAbelianization_weilAbelianizationEquivIntegralUnramified_symm K _

/-- The degree of `weilArtinMap K x` is the normalized valuation of `x`. -/
@[simp]
theorem weilDegreeAbelianization_weilArtinMap (x : Kˣ) :
    weilDegreeAbelianization K (weilArtinMap K x) = normalizedValuation K x := by
  apply zHat.ofInt_injective
  rw [← unramifiedCoordinate_weilToAbsoluteAbelianization,
    weilToAbsoluteAbelianization_weilArtinMap, unramifiedCoordinate_artinMap]

/-- The local Artin map into the abelianized Weil group is continuous. -/
theorem continuous_weilArtinMap : Continuous (weilArtinMap K) := by
  -- The topology of `W_K^ab` is induced by `x ↦ (x, deg x)` into `G_K^ab × ℤ`.
  have hΦ := isEmbedding_weilToAbsoluteAbelianization_prod_weilDegreeAbelianization K
  refine hΦ.continuous_iff.2 ?_
  convert (continuous_artinMap K).prodMk (continuous_normalizedValuation K) using 1
  ext x <;> simp

/-- **Every class of the abelianized Weil group is an Artin symbol**: the local Artin map
`Kˣ → W_K^ab` is surjective. -/
theorem surjective_weilArtinMap : Function.Surjective (weilArtinMap K) := fun y ↦ by
  obtain ⟨x, hx⟩ : weilToAbsoluteAbelianization K y ∈ (artinMap K).range := by
    rw [range_artinMap, ← range_weilToAbsoluteAbelianization]
    exact ⟨y, rfl⟩
  exact ⟨x, injective_weilToAbsoluteAbelianization K (by simpa using hx)⟩

/-- The local Artin map into the abelianized Weil group is open. This is the open mapping theorem
for the continuous surjection `weilArtinMap K` from the σ-compact group `Kˣ` onto the locally
compact group `W_K^ab`. -/
theorem isOpenMap_weilArtinMap : IsOpenMap (weilArtinMap K) :=
  (weilArtinMap K).isOpenMap_of_sigmaCompact (surjective_weilArtinMap K)
    (continuous_weilArtinMap K)

/-- The local Artin map into the abelianized Weil group has the same kernel as the absolute local
Artin map, namely the intersection of the norm subgroups (`ker_artinMap_eq_iInf`). -/
theorem ker_weilArtinMap : (weilArtinMap K).ker = (artinMap K).ker := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← weilToAbsoluteAbelianization_weilArtinMap,
    map_eq_one_iff _ (injective_weilToAbsoluteAbelianization K)]

end TauCeti.ClassFieldTheory
