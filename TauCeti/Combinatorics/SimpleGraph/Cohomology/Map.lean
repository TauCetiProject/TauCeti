/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

public import TauCeti.Combinatorics.SimpleGraph.Cohomology.Basic

/-!
# Changing the coefficients of the first cohomology of a graph

A homomorphism of coefficient groups `A →* B` sends the `1`-cochains of a simple graph to the
`1`-cochains and, since the coboundary of a vertex function `φ : V → A` is carried to the
coboundary of `f ∘ φ`, the first cohomology `H¹(G, A)` to `H¹(G, B)`. This is the map through
which a change of coefficient group acts on the first cohomology, and it is the map induced on
`H¹(G, kˣ)` by a monoid homomorphism `k → l`, the two coefficient groups being the units of the
coefficient rings and the parameters being recorded by unit-valued ratios.

The map on cohomology is injective as soon as the homomorphism of coefficient groups is. The
injectivity is the statement that a cochain whose image is a coboundary is itself a coboundary, and
this is a statement about paths: the product of the values of a cochain along a path from a
representative of the connected component of a vertex to that vertex is a vertex value whose image
is, by the hypothesis, a coboundary of a vertex function, and injectivity then makes the coboundary
of the path product the original cochain.

There is no corresponding surjectivity statement: a coboundary of `B` need not be the image of a
coboundary, since the values of a vertex function need not lie in the image of `f`.

## Main definitions

* `SimpleGraph.oneCochainsMap`: the homomorphism of `1`-cochains induced by a homomorphism of
  coefficient groups.
* `SimpleGraph.firstCohomologyMap`: the induced homomorphism `H¹(G, A) → H¹(G, B)`.

## Main results

* `SimpleGraph.oneCochainsMap_apply`: the image cochain takes values in the image of the
  homomorphism.
* `SimpleGraph.oneCochainsMap_coboundary`: a coboundary is sent to the coboundary of the composed
  vertex function.
* `SimpleGraph.oneCochainsMap_injective`: an injective homomorphism of coefficient groups induces
  an injective map on `1`-cochains.
* `SimpleGraph.firstCohomologyMap_mk`: the induced map sends the class of a cochain to the class of
  its image.
* `SimpleGraph.firstCohomologyMap_mk_eq_one_iff`: a cochain is a coboundary exactly when its image
  is a coboundary, for an injective homomorphism of coefficient groups.
* `SimpleGraph.firstCohomologyMap_injective`: **an injective homomorphism of coefficient groups
  induces an injective map on the first cohomology**.

## References

The first cohomology of a graph with coefficients in the units of a field is the group in which
C. Couture, *Skew-Zigzag Algebras*, Section 4, https://arxiv.org/abs/1509.08405, classifies
skew-zigzag parameters. The map above is the change of coefficients along a homomorphism of
coefficient groups: the map induced on the first cohomology by that homomorphism, which carries
the class of a parameter of coefficients `k` to the class of its image of coefficients `l`.
-/

public section

namespace SimpleGraph

universe u v z

variable {V : Type u} (G : SimpleGraph V)

/-- The homomorphism of `1`-cochains induced by a homomorphism of coefficient groups. -/
def oneCochainsMap {A : Type v} {B : Type z} [CommGroup A] [CommGroup B] (f : A →* B) :
    G.oneCochains A →* G.oneCochains B where
  toFun σ := ⟨fun d ↦ f ((σ : G.Dart → A) d), by
    rw [mem_oneCochains_iff]
    intro d
    show f ((σ : G.Dart → A) d.symm) = (f ((σ : G.Dart → A) d))⁻¹
    rw [oneCochains_apply_symm, map_inv]⟩
  map_one' := by
    ext d
    simp
  map_mul' σ τ := by
    ext d
    simp

variable {A : Type v} {B : Type z} [CommGroup A] [CommGroup B]

/-- The value of an image cochain on a dart is the image of the value of the cochain. -/
@[simp]
theorem oneCochainsMap_apply (f : A →* B) (σ : G.oneCochains A) (d : G.Dart) :
    (G.oneCochainsMap f σ : G.Dart → B) d = f ((σ : G.Dart → A) d) := (rfl)

/-- **A coboundary is carried to the coboundary of the composed vertex function.** -/
theorem oneCochainsMap_coboundary (f : A →* B) (φ : V → A) :
    G.oneCochainsMap f (G.coboundary A φ) = G.coboundary B (f ∘ φ) := by
  ext d
  simp [oneCochainsMap_apply, coboundary_apply, Function.comp_def]

/-- An injective homomorphism of coefficient groups induces an injective map on `1`-cochains. -/
theorem oneCochainsMap_injective (f : A →* B) (hf : Function.Injective f) :
    Function.Injective (G.oneCochainsMap f) := by
  intro σ τ h
  have h' : ∀ d : G.Dart, f ((σ : G.Dart → A) d) = f ((τ : G.Dart → A) d) := by
    intro d
    have h'' := congrFun (congrArg Subtype.val h) d
    rwa [oneCochainsMap_apply, oneCochainsMap_apply] at h''
  exact Subtype.ext (funext fun d => hf (h' d))

/-- **The product of the values of a cochain along a walk telescopes.** If the image of the
cochain is the coboundary of `ψ`, the value of the cochain on a dart is the quotient of the values
of `ψ` at the two ends of the dart, and these quotients telescope along a walk. -/
private theorem prod_eq_div (f : A →* B) (σ : G.oneCochains A) (ψ : V → B)
    (hψ : ∀ d : G.Dart, f ((σ : G.Dart → A) d) = ψ d.snd / ψ d.fst) :
    ∀ {v w : V} (q : G.Walk v w),
      f ((q.darts.map fun d ↦ (σ : G.Dart → A) d).prod) = ψ w / ψ v := by
  intro v w q
  induction q with
  | nil => rw [Walk.darts_nil, List.map_nil, List.prod_nil, div_self', map_one]
  | @cons u v w h p ih =>
    calc f (((Walk.cons h p).darts.map fun d ↦ (σ : G.Dart → A) d).prod)
        = f (((σ : G.Dart → A) (Dart.mk (u, v) h)))
            * f ((p.darts.map fun d ↦ (σ : G.Dart → A) d).prod) := by
            rw [Walk.darts_cons, List.map_cons, List.prod_cons, map_mul]
      _ = (ψ v / ψ u) * (ψ w / ψ v) := by rw [hψ _, ih]
      _ = ψ w / ψ u := by rw [div_mul_div_cancel']

/-- The chosen representative of the connected component of a vertex. -/
private noncomputable def componentRoot (v : V) : V :=
  (G.connectedComponentMk v).nonempty_supp.some

/-- A chosen walk from the representative of the connected component of a vertex to that vertex. -/
private noncomputable def componentPath (v : V) : G.Walk (componentRoot G v) v :=
  (SimpleGraph.ConnectedComponent.exact ((G.connectedComponentMk v).nonempty_supp.some_mem)).some

private theorem componentRoot_eq_of_adj {v w : V} (h : G.Adj v w) :
    componentRoot G w = componentRoot G v :=
  congrArg (fun C : G.ConnectedComponent => C.nonempty_supp.some)
    (SimpleGraph.ConnectedComponent.sound h.symm.reachable)

/-- **A cochain whose image is a coboundary is a coboundary**, for an injective homomorphism of
coefficient groups. The product of the values of the cochain along the walk from the representative
of the connected component of a vertex to that vertex is a vertex value whose image is a coboundary
of a vertex function, and injectivity makes its coboundary the cochain itself. -/
private theorem exists_coboundary_of_eq_coboundary_map (f : A →* B) (hf : Function.Injective f)
    {σ : G.oneCochains A} {ψ : V → B} (hψ : G.oneCochainsMap f σ = G.coboundary B ψ) :
    ∃ φ : V → A, G.coboundary A φ = σ := by
  have hψ' : ∀ d : G.Dart, f ((σ : G.Dart → A) d) = ψ d.snd / ψ d.fst := by
    intro d
    have h := congrFun (congrArg Subtype.val hψ) d
    rwa [oneCochainsMap_apply, coboundary_apply] at h
  have hprod : ∀ v : V,
      f (((componentPath G v).darts.map fun d ↦ (σ : G.Dart → A) d).prod)
        = ψ v / ψ (componentRoot G v) :=
    fun v => prod_eq_div G f σ ψ hψ' (componentPath G v)
  refine ⟨fun v => ((componentPath G v).darts.map fun d ↦ (σ : G.Dart → A) d).prod, ?_⟩
  apply Subtype.ext
  funext d
  have hroot : componentRoot G d.snd = componentRoot G d.fst :=
    (componentRoot_eq_of_adj G d.symm.adj).symm
  refine hf (by
    rw [coboundary_apply, map_div, hprod, hprod, hroot, hψ' d, div_div, mul_div_cancel])

/-- **The map on the first cohomology induced by a homomorphism of coefficient groups.** -/
def firstCohomologyMap (f : A →* B) : G.FirstCohomology A →* G.FirstCohomology B :=
  FirstCohomology.lift ((FirstCohomology.mk G B).comp (G.oneCochainsMap f)) (by
    rintro _ ⟨φ, rfl⟩
    refine MonoidHom.mem_ker.mpr ?_
    rw [MonoidHom.comp_apply, oneCochainsMap_coboundary, FirstCohomology.mk_coboundary])

/-- The induced map sends the cohomology class of a cochain to that of its image. -/
@[simp]
theorem firstCohomologyMap_mk (f : A →* B) (σ : G.oneCochains A) :
    G.firstCohomologyMap f (FirstCohomology.mk G A σ) =
      FirstCohomology.mk G B (G.oneCochainsMap f σ) := by
  rw [firstCohomologyMap, FirstCohomology.lift_mk, MonoidHom.comp_apply]

/-- **A `1`-cochain is a coboundary exactly when its image is a coboundary**, for an injective
homomorphism of coefficient groups. -/
theorem firstCohomologyMap_mk_eq_one_iff (f : A →* B) (hf : Function.Injective f)
    (σ : G.oneCochains A) :
    G.firstCohomologyMap f (FirstCohomology.mk G A σ) = 1 ↔ ∃ φ : V → A,
      G.coboundary A φ = σ := by
  rw [firstCohomologyMap_mk, FirstCohomology.mk_eq_one_iff]
  constructor
  · rintro ⟨ψ, hψ⟩
    exact exists_coboundary_of_eq_coboundary_map G f hf hψ.symm
  · rintro ⟨φ, hφ, rfl⟩
    exact ⟨f ∘ φ, by rw [oneCochainsMap_coboundary]⟩

/-- **An injective homomorphism of coefficient groups induces an injective map on the first
cohomology.** -/
theorem firstCohomologyMap_injective (f : A →* B) (hf : Function.Injective f) :
    Function.Injective (G.firstCohomologyMap f) := by
  rintro x y hxy
  obtain ⟨σ, rfl⟩ := FirstCohomology.mk_surjective x
  obtain ⟨τ, rfl⟩ := FirstCohomology.mk_surjective y
  rw [firstCohomologyMap_mk, firstCohomologyMap_mk] at hxy
  obtain ⟨ψ, hψ⟩ := FirstCohomology.mk_eq_mk_iff.mp hxy
  have hkey : G.oneCochainsMap f (τ * σ⁻¹) = G.coboundary B ψ := by
    calc G.oneCochainsMap f (τ * σ⁻¹) = G.oneCochainsMap f τ * (G.oneCochainsMap f σ)⁻¹ :=
          by rw [map_mul, map_inv]
      _ = (G.oneCochainsMap f σ * G.coboundary B ψ) * (G.oneCochainsMap f σ)⁻¹ := by rw [hψ]
      _ = G.coboundary B ψ * ((G.oneCochainsMap f σ) * (G.oneCochainsMap f σ)⁻¹) := by
        rw [mul_comm (G.oneCochainsMap f σ) (G.coboundary B ψ), mul_assoc]
      _ = G.coboundary B ψ := by rw [mul_inv_cancel, mul_one]
  obtain ⟨φ, hφ⟩ := exists_coboundary_of_eq_coboundary_map G f hf hkey
  refine FirstCohomology.mk_eq_mk_iff.mpr ⟨φ, ?_⟩
  calc τ = σ * (τ * σ⁻¹) := by
        rw [← mul_assoc, mul_comm (σ) (τ), mul_inv_cancel_right]
    _ = σ * G.coboundary A φ := by rw [hφ]

end SimpleGraph
