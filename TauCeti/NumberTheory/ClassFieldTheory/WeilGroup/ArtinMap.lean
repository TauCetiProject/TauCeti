/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.Unramified
public import TauCeti.NumberTheory.ClassFieldTheory.WeilGroup.Abelianization
import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Decomposition

/-!
# The image of the local Artin map

Let `K` be a nonarchimedean local field. The absolute local Artin map `artinMap K : Kˣ →* G_K^ab`
has dense image, but it is not surjective. This file identifies its image: it is the subgroup
`integralUnramifiedSubgroup K` of classes whose unramified coordinate in `ℤ̂` is an integer
(`range_artinMap`), which is also the image of the abelianized Weil group `W_K^ab → G_K^ab`
(`range_weilToAbsoluteAbelianization`). So a class in `G_K^ab` is an Artin symbol exactly when it
is the class of an element of the Weil group (`mem_range_artinMap_iff`).

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

## References

* J. Tate, *Number theoretic background*, in *Automorphic forms, representations and
  L-functions*, Proc. Sympos. Pure Math. 33, Part 2 (1979), §1.4.
* J.-P. Serre, *Local class field theory*, in J. W. S. Cassels and A. Fröhlich (eds.),
  *Algebraic Number Theory*, Chapter VI, §2.
-/

public section

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

end TauCeti.ClassFieldTheory
