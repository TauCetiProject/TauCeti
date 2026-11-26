/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Duality.Manifold
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Degree

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

## Main definitions

* `TopCat.shriek`: the shriek map `D_X ∘ f^* ∘ D_Y⁻¹`.
* `TauCeti.HomologicalOrientation.shriek`: the shriek map of a continuous map between closed
  oriented manifolds.

## Main results

* `TopCat.shriek_singularCapAddHom`: `f_!(z_Y ⌢ α) = z_X ⌢ f^*α`.
* `TopCat.shriek_id`, `TopCat.shriek_comp`: functoriality.
* `TopCat.map_shriek`: if `f_* z_X = d • z_Y`, then `f_*(f_! y) = d • y`.
* `TauCeti.HomologicalOrientation.map_shriek` and
  `TauCeti.HomologicalOrientation.map_shriek_eq_degree_smul`: `f_* ∘ f_! = deg(f) • id` for a map
  of closed oriented manifolds of the same dimension.
* `TauCeti.HomologicalOrientation.zsmul_eq_zero_of_shriek_eq_zero`: the kernel of `f_!` is
  `deg(f)`-torsion.

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
  rw [shriek_singularCapAddHom, singularCapAddHom_naturality, hd]
  simp [singularCapAddHom_apply]

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

end HomologicalOrientation

end TauCeti
