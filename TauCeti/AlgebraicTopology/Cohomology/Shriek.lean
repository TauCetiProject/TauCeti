/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Duality.Manifold
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Degree
import TauCeti.AlgebraicTopology.Cohomology.Cap.Unit

/-!
# Shriek maps through Poincaré duality

Let `f : X → Y` be a continuous map, `z_X ∈ H_m(X; T)` and `z_Y ∈ H_n(Y; T)` homology classes, and
write `D_X(α) = z_X ⌢ α` and `D_Y(α) = z_Y ⌢ α` for capping with them
(`TopCat.singularCapAddHom`). When `D_Y : Hᵖ(Y) → H_q(Y)` is bijective, as it is by Poincaré
duality for the fundamental class of a closed oriented manifold, the **shriek map** (Umkehr map,
wrong-way map) of `f` is

`f_! = D_X ∘ f^* ∘ D_Y⁻¹ : H_q(Y) → H_{q'}(X)`, `p + q = n`, `p + q' = m`

(`TopCat.shriek`), characterized by `f_!(z_Y ⌢ α) = z_X ⌢ f^*α` (`TopCat.shriek_singularCapAddHom`).
It shifts degrees by `m - n`. Shriek maps are functorial: the shriek map of the identity is the
identity (`TopCat.shriek_id`), and `(g ∘ f)_! = f_! ∘ g_!` (`TopCat.shriek_comp`).

By the projection formula `f_*(z_X ⌢ f^*α) = f_*z_X ⌢ α` (`TopCat.singularCap_naturality`), if
`f_* z_X = d • z_Y` for an integer `d`, then

`f_* ∘ f_! = d • id`

(`TopCat.map_shriek`). So the kernel of `f_!` consists of classes killed by `d`
(`TopCat.zsmul_eq_zero_of_shriek_eq_zero`), and `f_!` is injective when `d = ±1`
(`TopCat.injective_shriek_of_isUnit`). The other composite `f_! ∘ f_*` is not `d • id` in
general: for a degree-one map `T² → S²` collapsing the complement of a disc, `f_!` vanishes on
`H₁(S²) = 0`, so `f_! ∘ f_*` kills `H₁(T²) = ℤ²`.

If capping with the class of the constant unit cocycle is the identity, as it is for the
coefficient morphisms of fundamental classes, then `z_Y = z_Y ⌢ 1` and `f^*1 = 1`, so `f_!` sends
`z_Y` to `z_X` (`TopCat.shriek_apply_self`). In degree zero, for classes of the same degree with
`f_* z_X = d • z_Y`, the augmentation `ε : H₀ → M` satisfies `ε(f_! y) = d • ε(y)`
(`TopCat.singularHomology₀ε_shriek`): writing `y = z_Y ⌢ α`, both sides are Kronecker pairings,
`⟨f^*α, z_X⟩ = ⟨α, f_* z_X⟩`.

For closed oriented manifolds `M` and `N` of dimensions `m` and `n`, cap product with the
fundamental class is bijective by Poincaré duality
(`TauCeti.HomologicalOrientation.bijective_singularCapAddHom_fundamentalClass`), so every
continuous map `f : M → N` has a shriek map `f_! : H_q(N; L) → H_{q'}(M; L)` with coefficients in
every abelian group `L` (`TauCeti.HomologicalOrientation.shriek`). If `M` and `N`
have the same dimension and `f` has degree `d`, that is `f_*[M] = d • [N]`, then
`f_* ∘ f_! = d • id` on `H_*(N; L)` (`TauCeti.HomologicalOrientation.map_shriek`), and the kernel
of `f_!` is `d`-torsion (`TauCeti.HomologicalOrientation.zsmul_eq_zero_of_shriek_eq_zero`). When
`N` is preconnected, `d` is the degree `deg f` of `f`
(`TauCeti.HomologicalOrientation.degree`), so `f_* ∘ f_! = deg f • id`
(`TauCeti.HomologicalOrientation.map_shriek_eq_degree_smul`). For instance, for the double
cover `z ↦ z²` of the circle, of degree `2`, `f_* ∘ f_!` is multiplication by `2` on `H_*(S¹)`.

For every map of closed oriented manifolds, of any dimensions, `f_![N] = [M]`
(`TauCeti.HomologicalOrientation.shriek_fundamentalClass`). In degree zero, for manifolds of the
same dimension, the augmentation of `f_!(y)` is `deg f` times that of `y`
(`TauCeti.HomologicalOrientation.singularHomology₀ε_shriek_eq_degree_smul`); so when `M` is
path-connected, `f_!` sends the class of a point of `N` to `deg f` times the class of a point of
`M` (`TauCeti.HomologicalOrientation.shriek_singularHomology₀Section_eq_degree_smul`). For an
orientation-preserving covering with `d` sheets this is the sum of the classes of the `d`
preimages of the point.

## Main definitions

* `TopCat.shriek`: the shriek map `D_X ∘ f^* ∘ D_Y⁻¹`.
* `TauCeti.HomologicalOrientation.shriek`: the shriek map of a continuous map between closed
  oriented manifolds.

## Main results

* `TopCat.shriek_singularCapAddHom`: `f_!(z_Y ⌢ α) = z_X ⌢ f^*α`.
* `TopCat.shriek_id`, `TopCat.shriek_comp`: functoriality.
* `TopCat.map_shriek`: if `f_* z_X = d • z_Y`, then `f_*(f_! y) = d • y`.
* `TopCat.shriek_apply_self`: `f_!(z_Y) = z_X` when capping with the unit class is the identity.
* `TopCat.singularHomology₀ε_shriek`: if `f_* z_X = d • z_Y`, then `ε(f_! y) = d • ε(y)` in degree
  zero.
* `TauCeti.HomologicalOrientation.map_shriek` and
  `TauCeti.HomologicalOrientation.map_shriek_eq_degree_smul`: `f_* ∘ f_! = deg(f) • id` for a map
  of closed oriented manifolds of the same dimension.
* `TauCeti.HomologicalOrientation.zsmul_eq_zero_of_shriek_eq_zero`: the kernel of `f_!` is
  `deg(f)`-torsion.
* `TauCeti.HomologicalOrientation.shriek_fundamentalClass`: `f_![N] = [M]`.
* `TauCeti.HomologicalOrientation.singularHomology₀ε_shriek_eq_degree_smul` and
  `TauCeti.HomologicalOrientation.shriek_singularHomology₀Section_eq_degree_smul`: in degree zero
  `f_!` multiplies augmentations, and the classes of points, by `deg(f)`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3 (Poincaré duality, the cap product and its naturality).
* A. Dold, *Lectures on Algebraic Topology*, Springer, 1972, Chapter VIII (the Umkehr
  homomorphism of a map of manifolds).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Proposition 10.6.1 and
  Proposition 11.3.2.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology

universe w

namespace TopCat

section Shriek

variable {R₀ : Type w} [CommRing R₀] (k : Type*) [Ring k] [Linear k (ModuleCat.{w} R₀)]
  [MonoidalLinear k (ModuleCat.{w} R₀)] {R S T M P : ModuleCat.{w} R₀}
  (u : T ⟶ R ⊗ S) (μ : M ⊗ S ⟶ P)

variable {X Y Z : TopCat.{w}} {p q q' q'' m n l : ℕ}

/-- **The shriek map** `f_! = D_X ∘ f^* ∘ D_Y⁻¹ : H_q(Y; P) →+ H_{q'}(X; P)` of `f : X ⟶ Y`, for
classes `z_X ∈ H_m(X; T)` and `z_Y ∈ H_n(Y; T)` with `p + q' = m` and `p + q = n`, such that
capping with `z_Y` is a bijection `D_Y : Hᵖ(Y; R, M) → H_q(Y; P)`. Here `D_X` caps with `z_X`. -/
def shriek (f : X ⟶ Y) (hX : p + q' = m) (hY : p + q = n)
    (zX : ((singularHomologyFunctor (ModuleCat.{w} R₀) m).obj T).obj X)
    (zY : ((singularHomologyFunctor (ModuleCat.{w} R₀) n).obj T).obj Y)
    (hzY : Function.Bijective (Y.singularCapAddHom k u μ hY zY)) :
    ((singularHomologyFunctor (ModuleCat.{w} R₀) q).obj P).obj Y →+
      ((singularHomologyFunctor (ModuleCat.{w} R₀) q').obj P).obj X :=
  (X.singularCapAddHom k u μ hX zX).comp <|
    (TopCat.singularCohomologyMap f p).hom.toAddMonoidHom.comp
      (AddEquiv.ofBijective _ hzY).symm.toAddMonoidHom

variable {k u μ}

/-- **Characteristic property of the shriek map**: `f_!(z_Y ⌢ α) = z_X ⌢ f^*α`. -/
@[simp]
theorem shriek_singularCapAddHom (f : X ⟶ Y) (hX : p + q' = m) (hY : p + q = n)
    (zX : ((singularHomologyFunctor (ModuleCat.{w} R₀) m).obj T).obj X)
    (zY : ((singularHomologyFunctor (ModuleCat.{w} R₀) n).obj T).obj Y)
    (hzY : Function.Bijective (Y.singularCapAddHom k u μ hY zY))
    (α : Y.singularCohomology R k M p) :
    shriek k u μ f hX hY zX zY hzY (Y.singularCapAddHom k u μ hY zY α) =
      X.singularCapAddHom k u μ hX zX ((TopCat.singularCohomologyMap f p).hom α) := by
  have hα : (AddEquiv.ofBijective _ hzY).symm (Y.singularCapAddHom k u μ hY zY α) = α :=
    (AddEquiv.ofBijective _ hzY).symm_apply_apply α
  simp [shriek, hα]

/-- The shriek map is determined by its characteristic property: an additive map `g` with
`g(z_Y ⌢ α) = z_X ⌢ f^*α` for every `α` is `f_!`. -/
theorem shriek_unique (f : X ⟶ Y) (hX : p + q' = m) (hY : p + q = n)
    (zX : ((singularHomologyFunctor (ModuleCat.{w} R₀) m).obj T).obj X)
    (zY : ((singularHomologyFunctor (ModuleCat.{w} R₀) n).obj T).obj Y)
    (hzY : Function.Bijective (Y.singularCapAddHom k u μ hY zY))
    {g : ((singularHomologyFunctor (ModuleCat.{w} R₀) q).obj P).obj Y →+
      ((singularHomologyFunctor (ModuleCat.{w} R₀) q').obj P).obj X}
    (hg : ∀ α : Y.singularCohomology R k M p, g (Y.singularCapAddHom k u μ hY zY α) =
      X.singularCapAddHom k u μ hX zX ((TopCat.singularCohomologyMap f p).hom α)) :
    g = shriek k u μ f hX hY zX zY hzY := by
  ext y
  obtain ⟨α, rfl⟩ := hzY.2 y
  rw [hg, shriek_singularCapAddHom]

/-- **The shriek map of the identity** is the identity. -/
@[simp]
theorem shriek_id (hY : p + q = n)
    (zY : ((singularHomologyFunctor (ModuleCat.{w} R₀) n).obj T).obj Y)
    (hzY : Function.Bijective (Y.singularCapAddHom k u μ hY zY)) :
    shriek k u μ (𝟙 Y) hY hY zY zY hzY = AddMonoidHom.id _ := by
  refine (shriek_unique (𝟙 Y) hY hY zY zY hzY fun α ↦ ?_).symm
  rw [TopCat.singularCohomologyMap_id, ModuleCat.id_apply, AddMonoidHom.id_apply]

/-- **Functoriality of shriek maps**: `(g ∘ f)_! = f_! ∘ g_!`. -/
theorem shriek_comp (f : X ⟶ Y) (g : Y ⟶ Z) (hX : p + q'' = m) (hY : p + q' = l)
    (hZ : p + q = n) (zX : ((singularHomologyFunctor (ModuleCat.{w} R₀) m).obj T).obj X)
    (zY : ((singularHomologyFunctor (ModuleCat.{w} R₀) l).obj T).obj Y)
    (zZ : ((singularHomologyFunctor (ModuleCat.{w} R₀) n).obj T).obj Z)
    (hzY : Function.Bijective (Y.singularCapAddHom k u μ hY zY))
    (hzZ : Function.Bijective (Z.singularCapAddHom k u μ hZ zZ)) :
    shriek k u μ (f ≫ g) hX hZ zX zZ hzZ =
      (shriek k u μ f hX hY zX zY hzY).comp (shriek k u μ g hY hZ zY zZ hzZ) := by
  refine (shriek_unique (f ≫ g) hX hZ zX zZ hzZ fun α ↦ ?_).symm
  rw [AddMonoidHom.comp_apply, shriek_singularCapAddHom, shriek_singularCapAddHom,
    TopCat.singularCohomologyMap_comp, ModuleCat.comp_apply]

/-- **`f_* ∘ f_! = d • id`**: if `f_* z_X = d • z_Y`, then pushing forward the shriek image of a
class `y` gives `d • y`. -/
theorem map_shriek (f : X ⟶ Y) (hY : p + q = n)
    (zX : ((singularHomologyFunctor (ModuleCat.{w} R₀) n).obj T).obj X)
    (zY : ((singularHomologyFunctor (ModuleCat.{w} R₀) n).obj T).obj Y)
    (hzY : Function.Bijective (Y.singularCapAddHom k u μ hY zY)) {d : ℤ}
    (hd : (((singularHomologyFunctor (ModuleCat.{w} R₀) n).obj T).map f).hom zX = d • zY)
    (y : ((singularHomologyFunctor (ModuleCat.{w} R₀) q).obj P).obj Y) :
    (((singularHomologyFunctor (ModuleCat.{w} R₀) q).obj P).map f).hom
        (shriek k u μ f hY hY zX zY hzY y) = d • y := by
  obtain ⟨α, rfl⟩ := hzY.2 y
  rw [shriek_singularCapAddHom, singularCapAddHom_naturality, hd, singularCapAddHom_zsmul,
    AddMonoidHom.smul_apply]

/-- If `f_* z_X = d • z_Y`, the kernel of the shriek map consists of classes killed by `d`. -/
theorem zsmul_eq_zero_of_shriek_eq_zero (f : X ⟶ Y) (hY : p + q = n)
    (zX : ((singularHomologyFunctor (ModuleCat.{w} R₀) n).obj T).obj X)
    (zY : ((singularHomologyFunctor (ModuleCat.{w} R₀) n).obj T).obj Y)
    (hzY : Function.Bijective (Y.singularCapAddHom k u μ hY zY)) {d : ℤ}
    (hd : (((singularHomologyFunctor (ModuleCat.{w} R₀) n).obj T).map f).hom zX = d • zY)
    {y : ((singularHomologyFunctor (ModuleCat.{w} R₀) q).obj P).obj Y}
    (hy : shriek k u μ f hY hY zX zY hzY y = 0) :
    d • y = 0 := by
  rw [← map_shriek f hY zX zY hzY hd y, hy, map_zero]

/-- If `f_* z_X = d • z_Y` with `d = ±1`, the shriek map is injective. -/
theorem injective_shriek_of_isUnit (f : X ⟶ Y) (hY : p + q = n)
    (zX : ((singularHomologyFunctor (ModuleCat.{w} R₀) n).obj T).obj X)
    (zY : ((singularHomologyFunctor (ModuleCat.{w} R₀) n).obj T).obj Y)
    (hzY : Function.Bijective (Y.singularCapAddHom k u μ hY zY)) {d : ℤ} (hd₁ : IsUnit d)
    (hd : (((singularHomologyFunctor (ModuleCat.{w} R₀) n).obj T).map f).hom zX = d • zY) :
    Function.Injective (shriek k u μ f hY hY zX zY hzY) := by
  refine (injective_iff_map_eq_zero _).2 fun y hy ↦ ?_
  exact hd₁.smul_eq_zero.1 (zsmul_eq_zero_of_shriek_eq_zero f hY zX zY hzY hd hy)

end Shriek

section Unit

variable {R₀ : Type w} [CommRing R₀] {k : Type*} [Ring k] [Linear k (ModuleCat.{w} R₀)]
  [MonoidalLinear k (ModuleCat.{w} R₀)] {R S T M : ModuleCat.{w} R₀}

variable {X Y : TopCat.{w}} {m n : ℕ}

/-- **The shriek map sends `z_Y` to `z_X`**: if the coefficient morphisms make the class of the
constant `0`-cocycle with value `e` a unit for the cap product, `u ≫ e ▷ S ≫ μ = 𝟙`, then
`f_!(z_Y) = z_X`. For fundamental classes this is `f_![Y] = [X]`. -/
theorem shriek_apply_self (u : T ⟶ R ⊗ S) (μ : M ⊗ S ⟶ T) (e : R ⟶ M)
    (he : u ≫ e ▷ S ≫ μ = 𝟙 T) (f : X ⟶ Y) (hX : 0 + m = m) (hY : 0 + n = n)
    (zX : ((singularHomologyFunctor (ModuleCat.{w} R₀) m).obj T).obj X)
    (zY : ((singularHomologyFunctor (ModuleCat.{w} R₀) n).obj T).obj Y)
    (hzY : Function.Bijective (Y.singularCapAddHom k u μ hY zY)) :
    shriek k u μ f hX hY zX zY hzY zY = zX := by
  refine (congrArg (shriek k u μ f hX hY zX zY hzY)
    (singularCapAddHom_constSingularCocycle_of_comp_eq_id k he hY zY)).symm.trans ?_
  rw [shriek_singularCapAddHom, singularCohomologyMap_homologyπ_constSingularCocycle,
    singularCapAddHom_constSingularCocycle_of_comp_eq_id k he]

/-- **The shriek map in degree zero**: for classes `z_X`, `z_Y` of the same degree `n` with
`f_* z_X = d • z_Y`, the augmentation of `f_!(y)` is `d` times that of `y`, for every
`y ∈ H₀(Y; M)`. -/
theorem singularHomology₀ε_shriek (f : X ⟶ Y) (hn : n + 0 = n)
    (zX : ((singularHomologyFunctor (ModuleCat.{w} R₀) n).obj R).obj X)
    (zY : ((singularHomologyFunctor (ModuleCat.{w} R₀) n).obj R).obj Y)
    (hzY : Function.Bijective (Y.singularCapAddHom k (ρ_ R).inv (ρ_ M).hom hn zY)) {d : ℤ}
    (hd : (((singularHomologyFunctor (ModuleCat.{w} R₀) n).obj R).map f).hom zX = d • zY)
    (y : ((singularHomologyFunctor (ModuleCat.{w} R₀) 0).obj M).obj Y) :
    (X.singularHomology₀ε M).hom (shriek k (ρ_ R).inv (ρ_ M).hom f hn hn zX zY hzY y) =
      d • (Y.singularHomology₀ε M).hom y := by
  obtain ⟨α, rfl⟩ := hzY.2 y
  -- Both augmentations are Kronecker pairings: `ε(z_X ⌢ f^*α) = ⟨f^*α, z_X⟩` and
  -- `ε(z_Y ⌢ α) = ⟨α, z_Y⟩`.
  rw [shriek_singularCapAddHom]
  simp only [singularCapAddHom_apply, ← ModuleCat.comp_apply, singularCap_comp_singularHomology₀ε]
  -- Then `⟨f^*α, z_X⟩ = ⟨α, f_* z_X⟩ = d • ⟨α, z_Y⟩`.
  rw [singularKronecker_naturality, ModuleCat.comp_apply, hd, map_zsmul]

end Unit

end TopCat

namespace TauCeti

attribute [local instance] MonoidalPreadditive.monoidalLinearInt

namespace HomologicalOrientation

open Module

variable {M N O E F G : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  [TopologicalSpace N] [T2Space N] [CompactSpace N]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [ChartedSpace F N]
  [TopologicalSpace O] [T2Space O] [CompactSpace O]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [ChartedSpace G O]
  {m n l : ℕ} {p q q' q'' : ℕ}

section Shriek

variable (oM : HomologicalOrientation M E m) (hm : finrank ℝ E = m)
  (oN : HomologicalOrientation N F n) (hn : finrank ℝ F = n) (L : ModuleCat.{0} ℤ)

/-- **The shriek map** `f_! = D_M ∘ f^* ∘ D_N⁻¹ : H_q(N; L) →+ H_{q'}(M; L)` of a continuous map
`f : M → N` between closed oriented manifolds of dimensions `m` and `n`, for `p + q = n` and
`p + q' = m`, where `D_M` and `D_N` cap with the fundamental classes; `D_N` is invertible by
Poincaré duality (`TauCeti.HomologicalOrientation.bijective_singularCapAddHom_fundamentalClass`).
It lowers degrees by `n - m`. -/
def shriek (f : C(M, N)) (hq : p + q = n) (hq' : p + q' = m) :
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).obj (TopCat.of N) →+
      ((singularHomologyFunctor (ModuleCat.{0} ℤ) q').obj L).obj (TopCat.of M) :=
  TopCat.shriek ℤ (ρ_ _).inv (ρ_ L).hom (TopCat.ofHom f) hq' hq (oM.fundamentalClass hm)
    (oN.fundamentalClass hn) (oN.bijective_singularCapAddHom_fundamentalClass hn L p q hq)

/-- Unfolding `HomologicalOrientation.shriek` to the shriek map `TopCat.shriek` of the fundamental
classes. -/
theorem shriek_def (f : C(M, N)) (hq : p + q = n) (hq' : p + q' = m) :
    oM.shriek hm oN hn L f hq hq' =
      TopCat.shriek ℤ (ρ_ _).inv (ρ_ L).hom (TopCat.ofHom f) hq' hq (oM.fundamentalClass hm)
        (oN.fundamentalClass hn) (oN.bijective_singularCapAddHom_fundamentalClass hn L p q hq) :=
  (rfl)

/-- **Characteristic property of the shriek map**: `f_!([N] ⌢ α) = [M] ⌢ f^*α`. -/
@[simp]
theorem shriek_singularCapAddHom (f : C(M, N)) (hq : p + q = n) (hq' : p + q' = m)
    (α : (TopCat.of N).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L p) :
    oM.shriek hm oN hn L f hq hq'
        ((TopCat.of N).singularCapAddHom ℤ (ρ_ _).inv (ρ_ L).hom hq (oN.fundamentalClass hn) α) =
      (TopCat.of M).singularCapAddHom ℤ (ρ_ _).inv (ρ_ L).hom hq' (oM.fundamentalClass hm)
        ((TopCat.singularCohomologyMap (TopCat.ofHom f) p).hom α) :=
  TopCat.shriek_singularCapAddHom _ _ _ _ _ _ _

/-- The shriek map of a continuous map `f : M → N` of closed oriented manifolds is determined by
its characteristic property: an additive map `g` with `g([N] ⌢ α) = [M] ⌢ f^*α` for every `α` is
`f_!`. -/
theorem shriek_unique (f : C(M, N)) (hq : p + q = n) (hq' : p + q' = m)
    {g : ((singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).obj (TopCat.of N) →+
      ((singularHomologyFunctor (ModuleCat.{0} ℤ) q').obj L).obj (TopCat.of M)}
    (hg : ∀ α : (TopCat.of N).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L p,
      g ((TopCat.of N).singularCapAddHom ℤ (ρ_ _).inv (ρ_ L).hom hq (oN.fundamentalClass hn) α) =
        (TopCat.of M).singularCapAddHom ℤ (ρ_ _).inv (ρ_ L).hom hq' (oM.fundamentalClass hm)
          ((TopCat.singularCohomologyMap (TopCat.ofHom f) p).hom α)) :
    g = oM.shriek hm oN hn L f hq hq' :=
  TopCat.shriek_unique _ _ _ _ _ _ hg

/-- **The shriek map of the identity** is the identity. -/
@[simp]
theorem shriek_id (hq : p + q = n) :
    oN.shriek hn oN hn L (ContinuousMap.id N) hq hq = AddMonoidHom.id _ :=
  TopCat.shriek_id hq _ _

/-- **Functoriality of shriek maps**: `(g ∘ f)_! = f_! ∘ g_!` for continuous maps `f : M → N` and
`g : N → O` of closed oriented manifolds. -/
theorem shriek_comp (oO : HomologicalOrientation O G l) (hl : finrank ℝ G = l) (f : C(M, N))
    (g : C(N, O)) (hq : p + q = l) (hq' : p + q' = n) (hq'' : p + q'' = m) :
    oM.shriek hm oO hl L (g.comp f) hq hq'' =
      (oM.shriek hm oN hn L f hq' hq'').comp (oN.shriek hn oO hl L g hq hq') :=
  TopCat.shriek_comp (TopCat.ofHom f) (TopCat.ofHom g) hq'' hq' hq _ _ _ _ _

end Shriek

section Degree

variable (oM : HomologicalOrientation M E n) (hm : finrank ℝ E = n)
  (oN : HomologicalOrientation N F n) (hn : finrank ℝ F = n) (L : ModuleCat.{0} ℤ)

/-- **`f_* ∘ f_! = deg(f) • id`**: for a continuous map `f : M → N` of closed oriented manifolds of
the same dimension `n` with `f_*[M] = d • [N]`, pushing forward the shriek image of a class
`y ∈ H_q(N; L)` gives `d • y`. -/
theorem map_shriek (f : C(M, N)) (hq : p + q = n) {d : ℤ}
    (hd : oM.mapFundamentalClass hm f = d • oN.fundamentalClass hn)
    (y : ((singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).obj (TopCat.of N)) :
    (((singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).map (TopCat.ofHom f)).hom
        (oM.shriek hm oN hn L f hq hq y) = d • y :=
  TopCat.map_shriek (TopCat.ofHom f) hq _ _ _ ((oM.mapFundamentalClass_def hm f).symm.trans hd) y

/-- For a continuous map `f : M → N` of closed oriented manifolds of the same dimension with
`f_*[M] = d • [N]`, the kernel of the shriek map consists of classes killed by `d`. -/
theorem zsmul_eq_zero_of_shriek_eq_zero (f : C(M, N)) (hq : p + q = n) {d : ℤ}
    (hd : oM.mapFundamentalClass hm f = d • oN.fundamentalClass hn)
    {y : ((singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).obj (TopCat.of N)}
    (hy : oM.shriek hm oN hn L f hq hq y = 0) :
    d • y = 0 :=
  TopCat.zsmul_eq_zero_of_shriek_eq_zero (TopCat.ofHom f) hq _ _ _
    ((oM.mapFundamentalClass_def hm f).symm.trans hd) hy

/-- The shriek map of a continuous map of degree `±1` between closed oriented manifolds of the
same dimension is injective. -/
theorem injective_shriek_of_isUnit (f : C(M, N)) (hq : p + q = n) {d : ℤ} (hd₁ : IsUnit d)
    (hd : oM.mapFundamentalClass hm f = d • oN.fundamentalClass hn) :
    Function.Injective (oM.shriek hm oN hn L f hq hq) :=
  TopCat.injective_shriek_of_isUnit (TopCat.ofHom f) hq _ _ _ hd₁
    ((oM.mapFundamentalClass_def hm f).symm.trans hd)

/-- **`f_* ∘ f_! = deg(f) • id`**: for a continuous map `f : M → N` of closed oriented manifolds of
the same dimension `n` with `N` preconnected, pushing forward the shriek image of a class
`y ∈ H_q(N; L)` gives `deg f • y`, where `deg f` is `TauCeti.HomologicalOrientation.degree`. -/
theorem map_shriek_eq_degree_smul [PreconnectedSpace N] (f : C(M, N)) (hq : p + q = n)
    (y : ((singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).obj (TopCat.of N)) :
    (((singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).map (TopCat.ofHom f)).hom
        (oM.shriek hm oN hn L f hq hq y) = oM.degree oN hm f • y :=
  oM.map_shriek hm oN hn L f hq (oM.mapFundamentalClass_eq_degree_smul oN hm hn f) y

end Degree

section Unit

variable (oM : HomologicalOrientation M E m) (hm : finrank ℝ E = m)
  (oN : HomologicalOrientation N F n) (hn : finrank ℝ F = n)

/-- **The shriek map sends the fundamental class to the fundamental class**: `f_![N] = [M]` for
every continuous map `f : M → N` of closed oriented manifolds, of any dimensions. -/
@[simp]
theorem shriek_fundamentalClass (f : C(M, N)) :
    oM.shriek hm oN hn (ModuleCat.of ℤ (ULift.{0} ℤ)) f (Nat.zero_add n) (Nat.zero_add m)
      (oN.fundamentalClass hn) = oM.fundamentalClass hm :=
  TopCat.shriek_apply_self _ _ (𝟙 _) (by simp) _ _ _ _ _ _

end Unit

section DegreeZero

variable (oM : HomologicalOrientation M E n) (hm : finrank ℝ E = n)
  (oN : HomologicalOrientation N F n) (hn : finrank ℝ F = n) (L : ModuleCat.{0} ℤ)

/-- **The shriek map in degree zero**: for a continuous map `f : M → N` of closed oriented
manifolds of the same dimension with `f_*[M] = d • [N]`, the augmentation of `f_!(y)` is `d` times
that of `y`, for every `y ∈ H₀(N; L)`. -/
theorem singularHomology₀ε_shriek (f : C(M, N)) {d : ℤ}
    (hd : oM.mapFundamentalClass hm f = d • oN.fundamentalClass hn)
    (y : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 0).obj L).obj (TopCat.of N)) :
    ((TopCat.of M).singularHomology₀ε L).hom (oM.shriek hm oN hn L f (Nat.add_zero n)
        (Nat.add_zero n) y) = d • ((TopCat.of N).singularHomology₀ε L).hom y :=
  TopCat.singularHomology₀ε_shriek _ _ _ _ _ ((oM.mapFundamentalClass_def hm f).symm.trans hd) y

/-- **The shriek map in degree zero**: for a continuous map `f : M → N` of closed oriented
manifolds of the same dimension with `N` preconnected, the augmentation of `f_!(y)` is `deg f`
times that of `y`, for every `y ∈ H₀(N; L)`. -/
theorem singularHomology₀ε_shriek_eq_degree_smul [PreconnectedSpace N] (f : C(M, N))
    (y : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 0).obj L).obj (TopCat.of N)) :
    ((TopCat.of M).singularHomology₀ε L).hom (oM.shriek hm oN hn L f (Nat.add_zero n)
        (Nat.add_zero n) y) = oM.degree oN hm f • ((TopCat.of N).singularHomology₀ε L).hom y :=
  oM.singularHomology₀ε_shriek hm oN hn L f (oM.mapFundamentalClass_eq_degree_smul oN hm hn f) y

/-- **The shriek map of the class of a point**: for a continuous map `f : M → N` of closed oriented
manifolds of the same dimension with `f_*[M] = d • [N]` and `M` path-connected, `f_!` sends the
class `[y] r ∈ H₀(N; L)` of a point `y` with coefficient `r` to `d • [x] r` for any point `x` of
`M`. -/
theorem shriek_singularHomology₀Section [PathConnectedSpace M] (f : C(M, N)) {d : ℤ}
    (hd : oM.mapFundamentalClass hm f = d • oN.fundamentalClass hn) (x : M) (y : N) (r : L) :
    oM.shriek hm oN hn L f (Nat.add_zero n) (Nat.add_zero n)
        ((singularHomology₀Section L (X := TopCat.of N) y).hom r) =
      d • (singularHomology₀Section L (X := TopCat.of M) x).hom r := by
  -- On a path-connected space the augmentation of zeroth homology is injective.
  refine (ConcreteCategory.injective_of_mono_of_preservesPullback
    ((TopCat.of M).singularHomology₀ε L)) ?_
  rw [oM.singularHomology₀ε_shriek hm oN hn L f hd]
  simp

/-- **The shriek map of the class of a point**: for a continuous map `f : M → N` of closed oriented
manifolds of the same dimension, `M` path-connected and `N` preconnected, `f_!` sends the class
`[y] r ∈ H₀(N; L)` of a point `y` to `deg f • [x] r` for any point `x` of `M`. -/
theorem shriek_singularHomology₀Section_eq_degree_smul [PathConnectedSpace M] [PreconnectedSpace N]
    (f : C(M, N)) (x : M) (y : N) (r : L) :
    oM.shriek hm oN hn L f (Nat.add_zero n) (Nat.add_zero n)
        ((singularHomology₀Section L (X := TopCat.of N) y).hom r) =
      oM.degree oN hm f • (singularHomology₀Section L (X := TopCat.of M) x).hom r :=
  oM.shriek_singularHomology₀Section hm oN hn L f
    (oM.mapFundamentalClass_eq_degree_smul oN hm hn f) x y r

end DegreeZero

end HomologicalOrientation

end TauCeti
