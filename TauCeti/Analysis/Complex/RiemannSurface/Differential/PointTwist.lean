/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Canonical.Basic
public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Cohomology
public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Cohomology
import TauCeti.Analysis.Complex.RiemannSurface.Differential.Sphere
import TauCeti.Topology.ContinuousOn.PuncturedNhds

/-!
# The point-twist sequence of differential sheaves

Let `ω` be a `1`-form on a Riemann surface `X` which is meromorphic and of finite order
everywhere. Division by `ω` identifies the sheaf `Ω_D` of meromorphic `1`-forms with divisor at
least `-D` with a divisor sheaf `𝒪_E`
(`TauCeti.RiemannSurface.differentialSheafIsoDivisorSheaf`), and these identifications commute
with the inclusions `Ω_D ⟶ Ω_D'` and `𝒪_E ⟶ 𝒪_E'`
(`TauCeti.RiemannSurface.differentialSheafMapOfLE_comp_differentialSheafIsoDivisorSheaf_hom`).
On a compact surface this is the naturality of `Ω_D ≅ 𝒪_(D + div ω)` in `D`
(`TauCeti.RiemannSurface.differentialSheafMapOfLE_comp_differentialSheafIsoDivisorSheafAdd_hom`).

Transporting the point-twist sequence `0 → 𝒪_(D + K) → 𝒪_(D + K + x) → ℂ_x → 0` of divisor
sheaves along these isomorphisms, for `K = div ω`, gives the short exact sequence
`0 → Ω_D → Ω_(D + x) → ℂ_x → 0`
(`TauCeti.RiemannSurface.differentialPointTwistSequence_shortExact`).
On a compact Hausdorff surface it follows that finiteness of `H¹(X, Ω_D)` does not change when a
point is added to `D`, and that adding a point raises `h⁰(Ω_D) - h¹(Ω_D)` by one once `H¹(X, Ω_D)`
is finite-dimensional. These are the point-twist steps of Riemann–Roch for the sheaves `Ω_D`.

These statements only need some meromorphic `1`-form to exist, so they are stated for a surface
with a canonical divisor (`TauCeti.RiemannSurface.IsCanonicalDivisor`); for every canonical
divisor `K` the cohomology of `Ω_D` is that of `𝒪_(D + K)`
(`TauCeti.RiemannSurface.nonempty_differentialSheafCechCohomologyIso_of_isCanonicalDivisor`).
A finite holomorphic map to the Riemann sphere supplies a canonical divisor, by pulling back
`dz` (see `TauCeti.Analysis.Complex.RiemannSurface.Differential.RiemannHurwitz`).
On the Riemann sphere, `div dz = -2[∞]`, so `Ω_D` has the cohomology of `𝒪_(D - 2[∞])`
(`TauCeti.RiemannSurface.nonempty_differentialSheafCechCohomologyIso_onePoint`).

## Main definitions

* `TauCeti.RiemannSurface.differentialSheafIsoDivisorSheafAddOfPoint`: the isomorphism
  `Ω_(D + x) ≅ 𝒪_(D + div ω + x)`.
* `TauCeti.RiemannSurface.differentialPointTwistSequence`: the sequence
  `Ω_D → Ω_(D + x) → ℂ_x`.

## Main results

* `TauCeti.RiemannSurface.differentialPointTwistSequence_shortExact`: it is short exact.
* `TauCeti.RiemannSurface.finiteDimensional_cechCohomology_one_differentialSheaf_add_point_iff`:
  `H¹(X, Ω_(D + x))` is finite-dimensional if and only if `H¹(X, Ω_D)` is.
* `TauCeti.RiemannSurface.finrank_differentialSheaf_pointTwist_euler_characteristic`:
  `χ(Ω_(D + x)) = χ(Ω_D) + 1`.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §§16–17 (the point-twist sequence, the sheaves `Ω_D` and `Ω_D ≅ 𝒪_(D + K)`).
-/

public noncomputable section

open CategoryTheory Filter Opposite TopologicalSpace Topology
open TauCeti.Topology
open scoped Manifold

namespace TauCeti.RiemannSurface

open _root_.TauCeti.AlgebraicGeometry (WeilDivisor)

universe u

section Naturality

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  {ω : OneForm X} {D D' E E' : WeilDivisor X}

/-- Two morphisms `Ω_D' ⟶ 𝒪_E'` and `Ω_D ⟶ 𝒪_E` which are both division by `ω` off a closed
discrete set commute with the inclusions. -/
private theorem differentialSheafMapOfLE_comp_eq_of_smul (hω : ∀ x, ω.MeromorphicAt x)
    (hω₀ : ∀ x, ω.order x ≠ ⊤) (h : D ≤ D') (hE : E ≤ E')
    (e' : differentialSheaf D' ⟶ divisorSheaf E') (e : differentialSheaf D ⟶ divisorSheaf E)
    (he' : ∀ (U : Opens X) (s : (differentialSheaf D').obj.obj (op U)),
      ∀ᶠ y in codiscrete U, (divisorSheafSectionsEquiv E' U (e'.hom.app (op U) s)).1 y • ω y =
        (differentialSheafSectionsEquiv D' U s).1 y)
    (he : ∀ (U : Opens X) (s : (differentialSheaf D).obj.obj (op U)),
      ∀ᶠ y in codiscrete U, (divisorSheafSectionsEquiv E U (e.hom.app (op U) s)).1 y • ω y =
        (differentialSheafSectionsEquiv D U s).1 y) :
    differentialSheafMapOfLE h ≫ e' = e ≫ divisorSheafMapOfLE hE := by
  have := ChartedSpace.t1Space ℂ X
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply (divisorSheafSectionsEquiv E' U.unop).injective
  apply Subtype.ext
  refine eq_of_eventuallyEq_codiscrete (Subtype.prop _) (Subtype.prop _) ?_
  refine eventually_codiscrete_iff_forall_eventually_nhdsNE.2 fun x ↦ ?_
  have ht : Tendsto (Subtype.val : U.unop → X) (𝓝[≠] x) (𝓝[≠] (x : X)) :=
    continuous_subtype_val.continuousAt.tendsto_nhdsNE (x := x) Subtype.val_injective
  have hlhs := he' U.unop ((differentialSheafMapOfLE h).hom.app U s)
  have hrhs := he U.unop s
  rw [eventually_codiscrete_iff_forall_eventually_nhdsNE] at hlhs hrhs
  filter_upwards [hlhs x, hrhs x, ht.eventually ((hω x).eventually_apply_ne_zero (hω₀ x)),
    ht.eventually ((D'.eventually_eq_zero_nhdsNE x).mono fun _ hy ↦ hy.le),
    ht.eventually ((E'.eventually_eq_zero_nhdsNE x).mono fun _ hy ↦ hy.le)]
    with y h₁ h₂ hy hD hE'
  refine smul_left_injective ℂ hy ?_
  -- Unfold both composites to the section maps of the two factors.
  change (divisorSheafSectionsEquiv E' U.unop (e'.hom.app U
      ((differentialSheafMapOfLE h).hom.app U s))).1 y • ω y =
    (divisorSheafSectionsEquiv E' U.unop ((divisorSheafMapOfLE hE).hom.app U
      (e.hom.app U s))).1 y • ω y
  rw [h₁, differentialSheafMapOfLE_app, ite_eq_left hD, divisorSheafMapOfLE_app,
    Set.indicator_of_mem (s := {y : U.unop | E' y ≤ 0}) hE', h₂]

/-- **Division by `ω` commutes with the inclusions of differential and divisor sheaves.** If `ω`
is meromorphic everywhere with `ord_x ω = E x - D x` and `ord_x ω = E' x - D' x`, `D ≤ D'` and
`E ≤ E'` (the latter follows from the former), then `Ω_D ⟶ Ω_D' ≅ 𝒪_E'` equals
`Ω_D ≅ 𝒪_E ⟶ 𝒪_E'`. -/
theorem differentialSheafMapOfLE_comp_differentialSheafIsoDivisorSheaf_hom
    (hω : ∀ x, ω.MeromorphicAt x) (ho : ∀ x, ω.order x = ((E x - D x : ℤ) : WithTop ℤ))
    (ho' : ∀ x, ω.order x = ((E' x - D' x : ℤ) : WithTop ℤ)) (h : D ≤ D') (hE : E ≤ E') :
    differentialSheafMapOfLE h ≫ (differentialSheafIsoDivisorSheaf ω hω ho').hom =
      (differentialSheafIsoDivisorSheaf ω hω ho).hom ≫ divisorSheafMapOfLE hE :=
  differentialSheafMapOfLE_comp_eq_of_smul hω (fun x ↦ by rw [ho x]; exact WithTop.coe_ne_top)
    h hE _ _ (differentialSheafIsoDivisorSheaf_hom_app_smul hω ho')
    (differentialSheafIsoDivisorSheaf_hom_app_smul hω ho)

variable [CompactSpace X]

/-- On a compact surface, the order of a `1`-form meromorphic and of finite order everywhere is
`E x - D x` for any divisors with `E = D + div ω`. -/
private theorem order_eq_coeff_sub_of_eq (hω : ∀ x, ω.MeromorphicAt x)
    (hω₀ : ∀ x, ω.order x ≠ ⊤) (hE : E = D + ω.divisor) (x : X) :
    ω.order x = ((E x - D x : ℤ) : WithTop ℤ) := by
  subst hE
  rw [← OneForm.coe_coeff_divisor hω (hω₀ x)]
  simp [AlgebraicGeometry.WeilDivisor.coeff]

/-- **`Ω_D ≅ 𝒪_(D + div ω)` is natural in `D`.** On a compact surface, for a `1`-form `ω`
meromorphic and of finite order everywhere and `D ≤ D'`, the inclusion `Ω_D ⟶ Ω_D'` corresponds
under division by `ω` to the inclusion `𝒪_(D + div ω) ⟶ 𝒪_(D' + div ω)`. -/
theorem differentialSheafMapOfLE_comp_differentialSheafIsoDivisorSheafAdd_hom
    (hω : ∀ x, ω.MeromorphicAt x) (hω₀ : ∀ x, ω.order x ≠ ⊤) (h : D ≤ D') :
    differentialSheafMapOfLE h ≫ (differentialSheafIsoDivisorSheafAdd ω hω hω₀ D').hom =
      (differentialSheafIsoDivisorSheafAdd ω hω hω₀ D).hom ≫
        divisorSheafMapOfLE ((add_le_add_iff_right ω.divisor).2 h) :=
  differentialSheafMapOfLE_comp_eq_of_smul hω hω₀ h _ _ _
    (differentialSheafIsoDivisorSheafAdd_hom_app_smul hω hω₀)
    (differentialSheafIsoDivisorSheafAdd_hom_app_smul hω hω₀)

end Naturality

/-! ### The point-twist sequence -/

section Sequence

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [CompactSpace X] (ω : OneForm X) (hω : ∀ x, ω.MeromorphicAt x) (hω₀ : ∀ x, ω.order x ≠ ⊤)
  (D : WeilDivisor X) (x : X)

/-- **`Ω_(D + x) ≅ 𝒪_(D + div ω + x)`.** On a compact surface, division by a `1`-form `ω`
meromorphic and of finite order everywhere identifies `Ω_(D + x)` with the divisor sheaf of
`D + div ω + x`, the point twist of the divisor sheaf `𝒪_(D + div ω) ≅ Ω_D`. Up to the equality
`D + x + div ω = D + div ω + x` it is `TauCeti.RiemannSurface.differentialSheafIsoDivisorSheafAdd`
at `D + x`. -/
def differentialSheafIsoDivisorSheafAddOfPoint :
    differentialSheaf (D + WeilDivisor.ofPoint x) ≅
      divisorSheaf (D + ω.divisor + WeilDivisor.ofPoint x) :=
  differentialSheafIsoDivisorSheaf ω hω
    (order_eq_coeff_sub_of_eq hω hω₀ (add_right_comm D ω.divisor (WeilDivisor.ofPoint x)))

/-- Off a closed discrete set, a section `η` of `Ω_(D + x)` and its image `η / ω` in
`𝒪_(D + div ω + x)` satisfy `(η / ω) ω = η`. -/
theorem differentialSheafIsoDivisorSheafAddOfPoint_hom_app_smul (U : Opens X)
    (s : (differentialSheaf (D + WeilDivisor.ofPoint x)).obj.obj (op U)) :
    ∀ᶠ y in codiscrete U,
      (divisorSheafSectionsEquiv (D + ω.divisor + WeilDivisor.ofPoint x) U
        ((differentialSheafIsoDivisorSheafAddOfPoint ω hω hω₀ D x).hom.hom.app (op U) s)).1 y •
          ω y = (differentialSheafSectionsEquiv (D + WeilDivisor.ofPoint x) U s).1 y :=
  differentialSheafIsoDivisorSheaf_hom_app_smul hω _ U s

/-- Division by `ω` carries the inclusion `Ω_D ⟶ Ω_(D + x)` to the inclusion
`𝒪_(D + div ω) ⟶ 𝒪_(D + div ω + x)`. -/
theorem differentialSheafMapOfLE_comp_differentialSheafIsoDivisorSheafAddOfPoint_hom :
    differentialSheafMapOfLE (WeilDivisor.le_add_ofPoint D x) ≫
        (differentialSheafIsoDivisorSheafAddOfPoint ω hω hω₀ D x).hom =
      (differentialSheafIsoDivisorSheafAdd ω hω hω₀ D).hom ≫
        divisorSheafMapOfLE (WeilDivisor.le_add_ofPoint (D + ω.divisor) x) :=
  differentialSheafMapOfLE_comp_eq_of_smul hω hω₀ _ _ _ _
    (differentialSheafIsoDivisorSheafAddOfPoint_hom_app_smul ω hω hω₀ D x)
    (differentialSheafIsoDivisorSheafAdd_hom_app_smul hω hω₀)

variable [∀ U : Opens X, Decidable (x ∈ U)]

/-- **The point-twist sequence `Ω_D → Ω_(D + x) → ℂ_x` of differential sheaves.** The first map
is the inclusion; the second divides by `ω` and extracts the newly allowed coefficient at `x` of
the resulting section of `𝒪_(D + div ω + x)` (`TauCeti.RiemannSurface.pointTwistMap`). -/
def differentialPointTwistSequence :
    ShortComplex (TopCat.Sheaf (ModuleCat.{u} ℂ) (TopCat.of X)) :=
  ShortComplex.mk (differentialSheafMapOfLE (WeilDivisor.le_add_ofPoint D x))
    ((differentialSheafIsoDivisorSheafAddOfPoint ω hω hω₀ D x).hom ≫
      pointTwistMap (D + ω.divisor) x) (by
        rw [← Category.assoc,
          differentialSheafMapOfLE_comp_differentialSheafIsoDivisorSheafAddOfPoint_hom,
          Category.assoc, divisorSheafMapOfLE_comp_pointTwistMap, Limits.comp_zero])

/-- The differential point-twist sequence is isomorphic, by division by `ω`, to the point-twist
sequence `𝒪_(D + div ω) → 𝒪_(D + div ω + x) → ℂ_x` of divisor sheaves. -/
def differentialPointTwistSequenceIso :
    differentialPointTwistSequence ω hω hω₀ D x ≅ ShortComplex.mk
      (divisorSheafMapOfLE (WeilDivisor.le_add_ofPoint (D + ω.divisor) x))
      (pointTwistMap (D + ω.divisor) x) (divisorSheafMapOfLE_comp_pointTwistMap _ x) :=
  ShortComplex.isoMk (differentialSheafIsoDivisorSheafAdd ω hω hω₀ D)
    (differentialSheafIsoDivisorSheafAddOfPoint ω hω hω₀ D x) (Iso.refl _)
    (differentialSheafMapOfLE_comp_differentialSheafIsoDivisorSheafAddOfPoint_hom
      ω hω hω₀ D x).symm
    (Category.comp_id _).symm

/-- **The point-twist sequence `0 → Ω_D → Ω_(D + x) → ℂ_x → 0` is short exact** on a compact
Riemann surface carrying a `1`-form `ω` meromorphic and of finite order everywhere. -/
theorem differentialPointTwistSequence_shortExact :
    (differentialPointTwistSequence ω hω hω₀ D x).ShortExact :=
  ShortComplex.shortExact_of_iso (differentialPointTwistSequenceIso ω hω hω₀ D x).symm
    (ShortComplex.shortExact_of_iso (pointTwistSequenceIso (D + ω.divisor) x)
      (pointTwistSequence_shortExact (D + ω.divisor) x))

end Sequence

/-! ### Cohomology -/

section Cohomology

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [CompactSpace X]

/-- **`Hⁿ(X, Ω_D) ≅ Hⁿ(X, 𝒪_(D + K))` for every canonical divisor `K`.** On a compact Riemann
surface, if `K` is the divisor of some `1`-form meromorphic and of finite order everywhere, the
degree `n` Čech cohomology of `Ω_D` is isomorphic to that of the divisor sheaf of `D + K`. -/
theorem nonempty_differentialSheafCechCohomologyIso_of_isCanonicalDivisor {K : WeilDivisor X}
    (hK : IsCanonicalDivisor K) (D : WeilDivisor X) (n : ℕ) :
    Nonempty ((cechCohomology (TopCat.of X) (ModuleCat.{u} ℂ) n).obj (differentialSheaf D).obj ≅
      (cechCohomology (TopCat.of X) (ModuleCat.{u} ℂ) n).obj (divisorSheaf (D + K)).obj) := by
  obtain ⟨ω, hω, hω₀, rfl⟩ := hK.exists_divisor_eq
  exact ⟨differentialSheafCechCohomologyIso ω hω hω₀ D n⟩

end Cohomology

section PointTwistCohomology

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [CompactSpace X] [T2Space X]

/-- An isomorphism of sheaves induces an isomorphism on degree `n` Čech cohomology. -/
private def cechCohomologyIsoOfIso {F G : TopCat.Sheaf (ModuleCat.{0} ℂ) (TopCat.of X)}
    (e : F ≅ G) (n : ℕ) :
    (cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).obj F.obj ≅
      (cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).obj G.obj :=
  (cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).mapIso ((sheafToPresheaf _ _).mapIso e)

private theorem finiteDimensional_iff_of_iso {M N : ModuleCat.{0} ℂ} (e : M ≅ N) :
    FiniteDimensional ℂ M ↔ FiniteDimensional ℂ N :=
  ⟨fun _ ↦ Module.Finite.equiv e.toLinearEquiv, fun _ ↦ Module.Finite.equiv e.symm.toLinearEquiv⟩

/-- **Finiteness of `H¹(X, Ω_D)` is unchanged by adding a point.** On a compact Hausdorff Riemann
surface with a canonical divisor, `H¹(X, Ω_(D + x))` is finite-dimensional if and only if
`H¹(X, Ω_D)` is. Finiteness is not asserted for any divisor. -/
theorem finiteDimensional_cechCohomology_one_differentialSheaf_add_point_iff
    (hK : ∃ K : WeilDivisor X, IsCanonicalDivisor K) (D : WeilDivisor X) (x : X) :
    FiniteDimensional ℂ ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) 1).obj
        (differentialSheaf (D + WeilDivisor.ofPoint x)).obj) ↔
      FiniteDimensional ℂ ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) 1).obj
        (differentialSheaf D).obj) := by
  classical
  obtain ⟨_, hK⟩ := hK
  obtain ⟨ω, hω, hω₀, -⟩ := hK.exists_divisor_eq
  rw [finiteDimensional_iff_of_iso
      (cechCohomologyIsoOfIso (differentialSheafIsoDivisorSheafAddOfPoint ω hω hω₀ D x) 1),
    finiteDimensional_iff_of_iso (differentialSheafCechCohomologyIso ω hω hω₀ D 1)]
  exact finiteDimensional_divisorCechCohomology_one_add_point_iff (D + ω.divisor) x

/-- **The point-twist step of Riemann–Roch for `Ω_D`.** On a compact connected Hausdorff Riemann
surface with a canonical divisor, once `H¹(X, Ω_D)` is finite-dimensional, adding a point raises
`h⁰(Ω_D) - h¹(Ω_D)` by one, where `h⁰` is the dimension of the global sections of `Ω_D` and `h¹`
that of its first Čech cohomology. -/
theorem finrank_differentialSheaf_pointTwist_euler_characteristic [ConnectedSpace X]
    (hK : ∃ K : WeilDivisor X, IsCanonicalDivisor K) (D : WeilDivisor X) (x : X)
    [FiniteDimensional ℂ ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) 1).obj
      (differentialSheaf D).obj)] :
    (Module.finrank ℂ ((differentialSheaf (D + WeilDivisor.ofPoint x)).obj.obj (op ⊤)) : ℤ) -
        Module.finrank ℂ ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) 1).obj
          (differentialSheaf (D + WeilDivisor.ofPoint x)).obj) =
      (Module.finrank ℂ ((differentialSheaf D).obj.obj (op ⊤)) : ℤ) -
        Module.finrank ℂ ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) 1).obj
          (differentialSheaf D).obj) + 1 := by
  classical
  obtain ⟨_, hK⟩ := hK
  obtain ⟨ω, hω, hω₀, -⟩ := hK.exists_divisor_eq
  let e := differentialSheafIsoDivisorSheafAdd ω hω hω₀ D
  let e' := differentialSheafIsoDivisorSheafAddOfPoint ω hω hω₀ D x
  have : FiniteDimensional ℂ (divisorCechCohomology (D + ω.divisor) 1) :=
    Module.Finite.equiv (differentialSheafCechCohomologyIso ω hω hω₀ D 1).toLinearEquiv
  have h₀ : Module.finrank ℂ ((differentialSheaf D).obj.obj (op ⊤)) =
      Module.finrank ℂ ((divisorSheaf (D + ω.divisor)).obj.obj (op ⊤)) :=
    (((sheafToPresheaf _ _).mapIso e).app (op ⊤)).toLinearEquiv.finrank_eq
  have h₀' : Module.finrank ℂ ((differentialSheaf (D + WeilDivisor.ofPoint x)).obj.obj (op ⊤)) =
      Module.finrank ℂ ((divisorSheaf (D + ω.divisor + WeilDivisor.ofPoint x)).obj.obj (op ⊤)) :=
    (((sheafToPresheaf _ _).mapIso e').app (op ⊤)).toLinearEquiv.finrank_eq
  rw [h₀, h₀', (differentialSheafCechCohomologyIso ω hω hω₀ D 1).toLinearEquiv.finrank_eq,
    (cechCohomologyIsoOfIso e' 1).toLinearEquiv.finrank_eq]
  exact finrank_pointTwist_euler_characteristic (D + ω.divisor) x

end PointTwistCohomology

open OnePoint in
/-- **Check on the Riemann sphere.** Since `div dz = -2[∞]`, the sheaf `Ω_D` on `OnePoint ℂ` has
the Čech cohomology of the divisor sheaf of `D - 2[∞]` in every degree. -/
theorem nonempty_differentialSheafCechCohomologyIso_onePoint (D : WeilDivisor (OnePoint ℂ))
    (n : ℕ) :
    Nonempty ((cechCohomology (TopCat.of (OnePoint ℂ)) (ModuleCat.{0} ℂ) n).obj
        (differentialSheaf D).obj ≅
      (cechCohomology (TopCat.of (OnePoint ℂ)) (ModuleCat.{0} ℂ) n).obj
        (divisorSheaf (D + (-2 : ℤ) • WeilDivisor.ofPoint (∞ : OnePoint ℂ))).obj) :=
  nonempty_differentialSheafCechCohomologyIso_of_isCanonicalDivisor
    isCanonicalDivisor_neg_two_infty D n

end TauCeti.RiemannSurface
