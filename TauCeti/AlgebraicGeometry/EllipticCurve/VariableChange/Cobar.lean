/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.HopfAlgebroid
public import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.SemidirectProduct
public import TauCeti.CategoryTheory.Groupoid.ActionCategory.Nerve

/-!
# The cobar complex of the Weierstrass Hopf algebroid

Let `A = ℤ[a₁, a₂, a₃, a₄, a₆]` and `Γ = A[u, u⁻¹, r, s, t]` be the Weierstrass Hopf algebroid
of `TauCeti/AlgebraicGeometry/EllipticCurve/VariableChange/HopfAlgebroid.lean`. Its iterated
tensor powers `Γ ⊗_A ⋯ ⊗_A Γ` corepresent chains of composable changes of variables, and for
each weight `k ∈ ℤ` they form the cobar complex of `(A, Γ)` with coefficients in the `k`-th
power `ω^k` of the Hodge line, whose cohomology Bauer computes on the way to the homotopy of
`tmf`. This file constructs that complex and identifies it in degrees `0` and `1` with the
structure maps of the Hopf algebroid. Its comparison with the cohomology of the moduli
stack of Weierstrass cubics is not part of this file.

The ring `Γ^{⊗n} = CobarRing n` is defined by `Γ^{⊗0} = A` and
`Γ^{⊗(n+1)} = Γ^{⊗n}[u, u⁻¹, r, s, t]` (`TauCeti.WeierstrassChange.ChangeRing`), the pushout
`Γ^{⊗n} ⊗_A Γ` of `Γ^{⊗n}` along the target of its last arrow. So `Γ^{⊗1}` is the arrow ring
`Γ` and `Γ^{⊗2}` is the ring `Γ ⊗_A Γ` of the coproduct. Ring homomorphisms `Γ^{⊗n} →+* R`
classify `n`-simplices of the nerve of the groupoid of Weierstrass curves over `R`
(`CobarRing.simplexEquiv`): a curve `W₀` with changes of variables `C₀, …, C_{n-1}`, read as the
chain `W₀ → W₁ → ⋯ → W_n` with `W_{i+1} = C_i • W_i`. These are the coordinates of
`TauCeti.ActionGroupoid.nerveEquiv` for the action of `VariableChange R` on
`WeierstrassCurve R`, and the change from `W₀` to `W_i` is the composite
`TauCeti.ActionGroupoid.vertexLabel C i = C_{i-1} * ⋯ * C₀`.

A map `θ : {0, …, m} → {0, …, n}` acts on such chains by restriction to the vertices `θ 0, …, θ m`
(`TauCeti.ActionGroupoid.nerveMap`); since every arrow is invertible, `θ` need not be monotone. The
classifying ring homomorphisms `cobarMap θ : Γ^{⊗m} →+* Γ^{⊗n}` therefore form a cosimplicial
commutative ring. For a weight `k ∈ ℤ`, a function `f` on `m`-simplices, read as a section of `ω^k`
trivialized by the invariant differential at the initial vertex, is pulled back along `θ` and
transported from the vertex `W_{θ 0}` back to `W₀`. The transport multiplies it by the `k`-th power
of the scaling factor `u` of the change between the two vertices (`cobarWeight`), matching the law
`f(C • W) = u⁻ᵏ f(W)` of a modular form of weight `k`. The result is the cosimplicial abelian group
`cobarObject k`, and its alternating coface complex is the cobar complex `cobarComplex k`.

The differential in degree `0` is `f ↦ uᵏ η_R(f) - η_L(f)` (`cobarDifferential_zero_apply`), so
for `k ≥ 0` the cocycles of degree `0` are exactly the integral modular forms of weight `k`
(`ker_cobarDifferential_zero`). In degree `1` the cofaces are the inclusions of the two tensor
factors and the coproduct `Δ`, and the differential is `γ ↦ u₁ᵏ (1 ⊗ γ) - Δ(γ) + γ ⊗ 1`
(`cobarDifferential_one_apply`).

## Main definitions

* `TauCeti.WeierstrassHopfAlgebroid.CobarRing n`: the ring `Γ^{⊗n}` of `n`-simplices.
* `TauCeti.WeierstrassHopfAlgebroid.CobarRing.simplexEquiv`: homomorphisms `Γ^{⊗n} →+* R`
  classify a Weierstrass curve with `n` composable changes of variables.
* `TauCeti.WeierstrassHopfAlgebroid.cobarMap`: the cosimplicial ring structure of `Γ^{⊗•}`.
* `TauCeti.WeierstrassHopfAlgebroid.cobarObject k`, `cobarComplex k`, `cobarDifferential k`: the
  weight-`k` cosimplicial abelian group, the cobar complex and its differential.

## Main results

* `TauCeti.WeierstrassHopfAlgebroid.cobarMap_comp`, `cobarMap_id`: functoriality of `cobarMap`.
* `TauCeti.WeierstrassHopfAlgebroid.cobarComplex_d`, `cobarDifferential_comp_cobarDifferential`:
  the differential of the cobar complex, which squares to zero.
* `TauCeti.WeierstrassHopfAlgebroid.cobarDifferential_zero_apply` and
  `ker_cobarDifferential_zero`: the degree-zero cocycles of weight `k` are the integral modular
  forms of weight `k`.
* `TauCeti.WeierstrassHopfAlgebroid.cobarMap_succAbove_zero_eq_rightUnit`,
  `cobarMap_succAbove_one_eq_coproduct` and the other low-degree cofaces, and
  `cobarDifferential_one_apply`: the comparison with the units and the coproduct of `(A, Γ)`.

## References

* T. Bauer, *Computation of the homotopy of the spectrum tmf*, in *Groups, homotopy and
  configuration spaces*, Geom. Topol. Monogr. 13 (2008), §§2–3 (the cobar complex of the
  Weierstrass Hopf algebroid).
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A1.2
  (the cobar complex of a Hopf algebroid).
-/

public section

noncomputable section

namespace TauCeti.WeierstrassHopfAlgebroid

open CategoryTheory MvPolynomial _root_.WeierstrassCurve TauCeti.WeierstrassChange
open TauCeti.ActionGroupoid

/-! ### The rings `Γ^{⊗n}` -/

/-- The rings `Γ^{⊗n}` as commutative rings: `Γ^{⊗0} = ℤ[a₁, ⋯, a₆]` and
`Γ^{⊗(n+1)} = Γ^{⊗n}[u, u⁻¹, r, s, t]`. The body is exposed and reducible so that
`Γ^{⊗(n+1)}` is the coefficient ring `ChangeRing (Γ^{⊗n})`, carrying its universal property, and
so that `Γ^{⊗1}` and `Γ^{⊗2}` are the rings `ArrowRing` and `ChangeRing ArrowRing` of the Hopf
algebroid, with the same instances. -/
@[reducible, expose] def cobarRingCat : ℕ → CommRingCat.{0}
  | 0 => .of (MvPolynomial Coeff ℤ)
  | n + 1 => .of (ChangeRing (cobarRingCat n))

/-- The ring `Γ^{⊗n} = Γ ⊗_A ⋯ ⊗_A Γ` of `n`-simplices of the nerve of the Weierstrass
groupoid. For `n = 0, 1, 2` it is `ℤ[a₁, ⋯, a₆]`, the arrow ring `Γ` and the ring
`Γ ⊗_A Γ = Γ[u, u⁻¹, r, s, t]` of the coproduct. -/
abbrev CobarRing (n : ℕ) : Type := cobarRingCat n

namespace CobarRing

variable (R : Type*) [CommRing R]

/-- **Homomorphisms out of `Γ^{⊗n}` classify `n`-simplices of the nerve**: a Weierstrass curve
`W₀` with `n` changes of variables `C₀, …, C_{n-1}`, the chain `W₀ → W₁ → ⋯ → W_n`. The last
arrow is the change classified by the coordinates `u, r, s, t` of
`Γ^{⊗n} = Γ^{⊗(n-1)}[u, u⁻¹, r, s, t]`. -/
def simplexEquiv : (n : ℕ) →
    (CobarRing n →+* R) ≃ WeierstrassCurve R × (Fin n → VariableChange R)
  | 0 =>
    { toFun k := (Universal.curve.map k, Fin.elim0)
      invFun p := p.1.specialize
      left_inv k := Universal.map_curve_injective (by simp)
      right_inv p := Prod.ext (by simp) (funext fun i ↦ i.elim0) }
  | n + 1 =>
    { toFun k :=
        ((simplexEquiv n (ChangeRing.lift.symm k).1).1,
          Fin.snoc (simplexEquiv n (ChangeRing.lift.symm k).1).2 (ChangeRing.lift.symm k).2)
      invFun p := ChangeRing.lift ((simplexEquiv n).symm (p.1, Fin.init p.2), p.2 (Fin.last n))
      left_inv k := by
        simp only [Fin.init_snoc, Fin.snoc_last, Prod.mk.eta, Equiv.symm_apply_apply]
        exact ChangeRing.lift.apply_symm_apply k
      right_inv p := by
        simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply, Fin.snoc_init_self] }

variable {R} {n : ℕ}

variable (n) in
/-- The inclusion `Γ^{⊗n} →+* Γ^{⊗(n+1)}` of the first `n` tensor factors, forgetting the last
arrow of a chain. -/
def includeLeft : CobarRing n →+* CobarRing (n + 1) :=
  algebraMap (CobarRing n) (ChangeRing (CobarRing n))

variable (n) in
/-- The last arrow `C_n` of the universal `(n + 1)`-simplex: the coordinates `u, r, s, t` of
`Γ^{⊗(n+1)} = Γ^{⊗n}[u, u⁻¹, r, s, t]`. -/
def lastChange : VariableChange (CobarRing (n + 1)) :=
  ChangeRing.universalChange (CobarRing n)

variable (n) in
/-- The inclusion `includeLeft n` is the structure map of `Γ^{⊗(n+1)} = Γ^{⊗n}[u, u⁻¹, r, s, t]`
as a `Γ^{⊗n}`-algebra. -/
theorem includeLeft_eq_algebraMap :
    includeLeft n = algebraMap (CobarRing n) (ChangeRing (CobarRing n)) :=
  (rfl)

variable (n) in
/-- The last arrow `lastChange n` is the universal change of variables of
`Γ^{⊗(n+1)} = Γ^{⊗n}[u, u⁻¹, r, s, t]`. -/
theorem lastChange_eq_universalChange :
    lastChange n = ChangeRing.universalChange (CobarRing n) :=
  (rfl)

theorem simplexEquiv_zero_apply (k : CobarRing 0 →+* R) :
    simplexEquiv R 0 k = (Universal.curve.map k, Fin.elim0) :=
  (rfl)

/-- `k : Γ^{⊗(n+1)} →+* R` classifies the chain of the `n`-simplex classified by its
restriction to the first `n` factors, followed by the last arrow classified by its coordinates
`u, r, s, t`. -/
theorem simplexEquiv_succ_apply (k : CobarRing (n + 1) →+* R) :
    simplexEquiv R (n + 1) k =
      ((simplexEquiv R n (k.comp (includeLeft n))).1,
        Fin.snoc (simplexEquiv R n (k.comp (includeLeft n))).2 ((lastChange n).map k)) := by
  rw [simplexEquiv, Equiv.coe_fn_mk, ChangeRing.lift_symm_apply, includeLeft_eq_algebraMap,
    lastChange_eq_universalChange]

/-- **Naturality of the classification**: composing with `g : R →+* S` extends the
coefficients of the classified simplex along `g`. -/
theorem simplexEquiv_comp {S : Type*} [CommRing S] (k : CobarRing n →+* R) (g : R →+* S) :
    simplexEquiv S n (g.comp k) =
      ((simplexEquiv R n k).1.map g, VariableChange.mapHom g ∘ (simplexEquiv R n k).2) := by
  induction n with
  | zero =>
    rw [simplexEquiv_zero_apply, simplexEquiv_zero_apply]
    exact Prod.ext (WeierstrassCurve.map_map _ _ _).symm (funext fun i ↦ i.elim0)
  | succ n ih =>
    rw [simplexEquiv_succ_apply, simplexEquiv_succ_apply, RingHom.comp_assoc, ih]
    refine Prod.ext rfl (funext fun i ↦ ?_)
    induction i using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last, Function.comp_apply]
      exact (VariableChange.map_map _ k g).symm
    | cast i => simp

end CobarRing

open CobarRing

/-- The universal `n`-simplex, classified by the identity of `Γ^{⊗n}`. -/
abbrev universalSimplex (n : ℕ) :
    WeierstrassCurve (CobarRing n) × (Fin n → VariableChange (CobarRing n)) :=
  simplexEquiv (CobarRing n) n (RingHom.id _)

/-- Every simplex classified by `k` is the coefficient extension of the universal one. -/
theorem simplexEquiv_eq {R : Type*} [CommRing R] {n : ℕ} (k : CobarRing n →+* R) :
    simplexEquiv R n k =
      ((universalSimplex n).1.map k, VariableChange.mapHom k ∘ (universalSimplex n).2) := by
  rw [← simplexEquiv_comp, RingHom.comp_id]

/-- Restriction of simplices commutes with coefficient extension along `g : R →+* S`. -/
private theorem nerveMap_mapHom {R S : Type*} [CommRing R] [CommRing S] {m n : ℕ}
    (θ : Fin (m + 1) → Fin (n + 1)) (x : WeierstrassCurve R × (Fin n → VariableChange R))
    (g : R →+* S) :
    nerveMap θ (x.1.map g, VariableChange.mapHom g ∘ x.2) =
      ((nerveMap θ x).1.map g, VariableChange.mapHom g ∘ (nerveMap θ x).2) :=
  nerveMap_map θ (VariableChange.mapHom g) (·.map g) (fun _ _ ↦ (map_variableChange ..).symm) x

/-! ### The cosimplicial ring `Γ^{⊗•}` -/

/-- The ring homomorphism `Γ^{⊗m} →+* Γ^{⊗n}` of `θ : {0, …, m} → {0, …, n}`, classifying the
restriction `nerveMap θ` of the universal `n`-simplex. In degrees `0` and `1` the cofaces are
the units and the coproduct of the Hopf algebroid (`cobarMap_succAbove_zero_eq_rightUnit`,
`cobarMap_succAbove_one_eq_coproduct`). -/
def cobarMap {m n : ℕ} (θ : Fin (m + 1) → Fin (n + 1)) : CobarRing m →+* CobarRing n :=
  (simplexEquiv (CobarRing n) m).symm (nerveMap θ (universalSimplex n))

/-- `k ∘ cobarMap θ` classifies the restriction along `θ` of the simplex classified by `k`. -/
@[simp]
theorem simplexEquiv_comp_cobarMap {R : Type*} [CommRing R] {m n : ℕ}
    (θ : Fin (m + 1) → Fin (n + 1)) (k : CobarRing n →+* R) :
    simplexEquiv R m (k.comp (cobarMap θ)) = nerveMap θ (simplexEquiv R n k) := by
  rw [simplexEquiv_comp, cobarMap, Equiv.apply_symm_apply, simplexEquiv_eq k,
    nerveMap_mapHom]

/-- `cobarMap θ` classifies the restriction along `θ` of the universal simplex. -/
@[simp]
theorem simplexEquiv_cobarMap {m n : ℕ} (θ : Fin (m + 1) → Fin (n + 1)) :
    simplexEquiv (CobarRing n) m (cobarMap θ) = nerveMap θ (universalSimplex n) :=
  Equiv.apply_symm_apply _ _

@[simp]
theorem cobarMap_id (n : ℕ) : cobarMap (id : Fin (n + 1) → Fin (n + 1)) = RingHom.id _ :=
  (simplexEquiv _ n).injective (by simp)

/-- Functoriality of `cobarMap`: `Γ^{⊗•}` is a cosimplicial commutative ring. -/
theorem cobarMap_comp {l m n : ℕ} (θ : Fin (m + 1) → Fin (n + 1))
    (ψ : Fin (l + 1) → Fin (m + 1)) :
    (cobarMap θ).comp (cobarMap ψ) = cobarMap (θ ∘ ψ) :=
  (simplexEquiv _ l).injective (by simp)

/-- Functoriality of `cobarMap`, evaluated at an element. -/
@[simp]
theorem cobarMap_cobarMap {l m n : ℕ} (θ : Fin (m + 1) → Fin (n + 1))
    (ψ : Fin (l + 1) → Fin (m + 1)) (f : CobarRing l) :
    cobarMap θ (cobarMap ψ f) = cobarMap (θ ∘ ψ) f :=
  RingHom.congr_fun (cobarMap_comp θ ψ) f

/-- The last coface `δⁿ⁺¹ : Γ^{⊗n} →+* Γ^{⊗(n+1)}`, forgetting the last arrow of a chain, is the
inclusion `includeLeft n` of the first `n` tensor factors. -/
theorem cobarMap_succAbove_last_eq_includeLeft (n : ℕ) :
    cobarMap (Fin.last (n + 1)).succAbove = includeLeft n := by
  refine (simplexEquiv _ n).injective ?_
  rw [simplexEquiv_cobarMap, universalSimplex, simplexEquiv_succ_apply, RingHom.id_comp]
  refine Prod.ext ?_ (funext fun j ↦ ?_)
  · simp
  · simp [Fin.succAbove_last]

/-! ### The weight-`k` cosimplicial abelian group and the cobar complex -/

/-- The scaling factor `u ∈ (Γ^{⊗n})ˣ` of the change of variables from the initial vertex `W₀` of
the universal `n`-simplex to its vertex `W_{θ 0}`. A section of `ω^k` trivialized at `W_{θ 0}`
is `u^k` times the corresponding section trivialized at `W₀`. -/
def cobarWeight {m n : ℕ} (θ : Fin (m + 1) → Fin (n + 1)) : (CobarRing n)ˣ :=
  (vertexLabel (universalSimplex n).2 (θ 0)).u

/-- The weight of `θ` is the scaling factor of the arrow from `W₀` to `W_{θ 0}`. -/
theorem cobarWeight_def {m n : ℕ} (θ : Fin (m + 1) → Fin (n + 1)) :
    cobarWeight θ = (vertexLabel (universalSimplex n).2 (θ 0)).u :=
  (rfl)

/-- `cobarMap θ` carries the change of variables from the initial vertex `W₀` to the vertex `W_i`
of the universal `m`-simplex to the change from `W_{θ 0}` to `W_{θ i}` of the universal
`n`-simplex. -/
theorem map_vertexLabel_universalSimplex {m n : ℕ} (θ : Fin (m + 1) → Fin (n + 1))
    (i : Fin (m + 1)) :
    (vertexLabel (universalSimplex m).2 i).map (cobarMap θ) =
      vertexLabel (universalSimplex n).2 (θ i) * (vertexLabel (universalSimplex n).2 (θ 0))⁻¹ := by
  have h := (simplexEquiv_eq (cobarMap θ)).symm.trans (simplexEquiv_cobarMap θ)
  simpa using congrArg (vertexLabel · i) (congrArg Prod.snd h)

/-- The scaling factors are a cocycle: transporting from `W_{θ (ψ 0)}` to `W_{θ 0}` and then to
`W₀` is transporting from `W_{θ (ψ 0)}` to `W₀`. -/
theorem map_cobarWeight_mul_cobarWeight {l m n : ℕ} (θ : Fin (m + 1) → Fin (n + 1))
    (ψ : Fin (l + 1) → Fin (m + 1)) :
    Units.map (cobarMap θ : CobarRing m →* CobarRing n) (cobarWeight ψ) * cobarWeight θ =
      cobarWeight (θ ∘ ψ) := by
  rw [cobarWeight_def, cobarWeight_def, cobarWeight_def, ← VariableChange.map_u,
    map_vertexLabel_universalSimplex, VariableChange.mul_inv_u, inv_mul_cancel_right,
    Function.comp_apply]

/-- A map `θ` keeping the initial vertex has trivial weight. -/
theorem cobarWeight_eq_one_of_apply_zero_eq_zero {m n : ℕ} {θ : Fin (m + 1) → Fin (n + 1)}
    (h : θ 0 = 0) : cobarWeight θ = 1 := by
  rw [cobarWeight_def, h, vertexLabel_zero, VariableChange.one_u]

@[simp]
theorem cobarWeight_id (n : ℕ) : cobarWeight (id : Fin (n + 1) → Fin (n + 1)) = 1 :=
  cobarWeight_eq_one_of_apply_zero_eq_zero rfl

/-- A map `θ` sending the initial vertex to `W₁` has the scaling factor `u₁` of the first arrow
`C₀ : W₀ → W₁` as its weight. -/
theorem cobarWeight_eq_of_apply_zero_eq_one {m n : ℕ} {θ : Fin (m + 1) → Fin (n + 2)}
    (h : θ 0 = 1) : cobarWeight θ = ((universalSimplex (n + 1)).2 0).u := by
  rw [cobarWeight_def, h, vertexLabel_one]

/-- The weight-`k` coface map `f ↦ u^k · θ^* f` of `θ : {0, …, m} → {0, …, n}`: a function on
`m`-simplices, read as a section of `ω^k` trivialized at the initial vertex, is pulled back along
`θ` and transported from the vertex `W_{θ 0}` back to `W₀` (`cobarWeight`). -/
def cobarAddMap (k : ℤ) {m n : ℕ} (θ : Fin (m + 1) → Fin (n + 1)) :
    CobarRing m →+ CobarRing n :=
  (AddMonoidHom.mulLeft ((cobarWeight θ ^ k : (CobarRing n)ˣ) : CobarRing n)).comp
    (cobarMap θ).toAddMonoidHom

@[simp]
theorem cobarAddMap_apply (k : ℤ) {m n : ℕ} (θ : Fin (m + 1) → Fin (n + 1)) (f : CobarRing m) :
    cobarAddMap k θ f = ↑(cobarWeight θ ^ k) * cobarMap θ f :=
  (rfl)

theorem cobarAddMap_id (k : ℤ) {n : ℕ} (f : CobarRing n) : cobarAddMap k id f = f := by
  simp

/-- Functoriality of the weight-`k` coface maps, from the cocycle property of `cobarWeight`. -/
theorem cobarAddMap_cobarAddMap (k : ℤ) {l m n : ℕ} (θ : Fin (m + 1) → Fin (n + 1))
    (ψ : Fin (l + 1) → Fin (m + 1)) (f : CobarRing l) :
    cobarAddMap k θ (cobarAddMap k ψ f) = cobarAddMap k (θ ∘ ψ) f := by
  have h : cobarMap θ ↑(cobarWeight ψ ^ k) =
      ↑(Units.map (cobarMap θ : CobarRing m →* CobarRing n) (cobarWeight ψ) ^ k) := by
    rw [← map_zpow, Units.coe_map, MonoidHom.coe_ofClass]
  rw [cobarAddMap_apply, cobarAddMap_apply, cobarAddMap_apply, map_mul, h, cobarMap_cobarMap,
    ← map_cobarWeight_mul_cobarWeight θ ψ, mul_zpow, Units.val_mul]
  ring

/-- The cosimplicial abelian group `Γ^{⊗•}` of weight `k`: its cofaces and codegeneracies act by
`cobarAddMap k`. Its alternating coface complex is the cobar complex `cobarComplex k`. -/
-- Exposed so that its objects unfold to `Γ^{⊗n}` in the terms of `cobarComplex k`.
@[expose] def cobarObject (k : ℤ) : CosimplicialObject AddCommGrpCat.{0} where
  obj n := AddCommGrpCat.of (CobarRing n.len)
  map θ := AddCommGrpCat.ofHom (cobarAddMap k θ.toOrderHom)
  map_id n := by
    ext f
    rw [AddCommGrpCat.hom_ofHom, AddCommGrpCat.hom_id, AddMonoidHom.id_apply,
      SimplexCategory.id_toOrderHom, OrderHom.id_coe]
    exact cobarAddMap_id k f
  map_comp θ ψ := by
    ext f
    rw [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply, AddCommGrpCat.hom_ofHom,
      AddCommGrpCat.hom_ofHom, AddCommGrpCat.hom_ofHom, SimplexCategory.comp_toOrderHom,
      OrderHom.comp_coe]
    exact (cobarAddMap_cobarAddMap k ψ.toOrderHom θ.toOrderHom f).symm

/-- The object of `cobarObject k` at `[n]` is `Γ^{⊗n}`. -/
@[simp]
theorem cobarObject_obj (k : ℤ) (n : SimplexCategory) :
    (cobarObject k).obj n = AddCommGrpCat.of (CobarRing n.len) :=
  (rfl)

/-- The map of `cobarObject k` along `θ` is the weight-`k` coface map of `θ`. -/
@[simp]
theorem cobarObject_map (k : ℤ) {m n : SimplexCategory} (θ : m ⟶ n) :
    (cobarObject k).map θ = AddCommGrpCat.ofHom (cobarAddMap k θ.toOrderHom) :=
  (rfl)

/-- The `i`-th coface of `cobarObject k` is the weight-`k` coface map of `i.succAbove`. -/
theorem cobarObject_δ (k : ℤ) {n : ℕ} (i : Fin (n + 2)) :
    (cobarObject k).δ i = AddCommGrpCat.ofHom (cobarAddMap k i.succAbove) := by
  rw [CosimplicialObject.δ, cobarObject_map, ← SimplexCategory.coe_δ]

/-- **The cobar complex of weight `k`** of the Weierstrass Hopf algebroid, the alternating coface
complex of `cobarObject k`. Its cohomology is the cohomology of `(A, Γ)` with coefficients in the
`k`-th power `ω^k` of the Hodge line. -/
-- Exposed so that its terms and differentials unfold to `Γ^{⊗n}` and `cobarDifferential`.
@[expose] def cobarComplex (k : ℤ) : CochainComplex AddCommGrpCat.{0} ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex _).obj (cobarObject k)

/-- The term of degree `n` of the cobar complex is `Γ^{⊗n}`. -/
@[simp]
theorem cobarComplex_X (k : ℤ) (n : ℕ) :
    (cobarComplex k).X n = AddCommGrpCat.of (CobarRing n) :=
  (rfl)

/-- The cobar differential `Γ^{⊗n} → Γ^{⊗(n+1)}` of weight `k`, the alternating sum of the
weight-`k` coface maps. -/
def cobarDifferential (k : ℤ) (n : ℕ) : CobarRing n →+ CobarRing (n + 1) :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • cobarAddMap k i.succAbove

theorem cobarDifferential_apply (k : ℤ) (n : ℕ) (f : CobarRing n) :
    cobarDifferential k n f =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • cobarAddMap k i.succAbove f := by
  simp [cobarDifferential]

/-- The differential of the cobar complex is the cobar differential. -/
theorem cobarComplex_d (k : ℤ) (n : ℕ) :
    (cobarComplex k).d n (n + 1) = AddCommGrpCat.ofHom (cobarDifferential k n) := by
  -- `AddCommGrpCat.ofHom` carries the alternating sum `cobarDifferential` to the alternating sum
  -- of the morphisms `ofHom (cobarAddMap k i.succAbove)`.
  have h : ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • AddCommGrpCat.ofHom (cobarAddMap k i.succAbove) =
      AddCommGrpCat.ofHom (cobarDifferential k n) := by
    apply AddCommGrpCat.homAddEquiv.injective
    rw [map_sum, AddCommGrpCat.homAddEquiv_apply, ConcreteCategory.hom_ofHom, cobarDifferential]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_zsmul, AddCommGrpCat.homAddEquiv_apply, ConcreteCategory.hom_ofHom]
  -- The complex is `CochainComplex.of` applied to Mathlib's alternating sum of the cofaces of
  -- `cobarObject k`, whose coface `δ i` acts by `cobarAddMap k i.succAbove`.
  dsimp only [cobarComplex, AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj]
  rw [CochainComplex.of_d, AlgebraicTopology.AlternatingCofaceMapComplex.objD, ← h]
  exact Finset.sum_congr rfl fun i _ ↦ congrArg ((-1 : ℤ) ^ (i : ℕ) • ·) (cobarObject_δ k i)

/-- The differential of the cobar complex acts by the cobar differential. -/
theorem cobarComplex_d_apply (k : ℤ) (n : ℕ) (f : CobarRing n) :
    (cobarComplex k).d n (n + 1) f = cobarDifferential k n f := by
  rw [cobarComplex_d]
  exact AddCommGrpCat.ofHom_apply (cobarDifferential k n) f

/-- The cobar differential squares to zero. -/
theorem cobarDifferential_comp_cobarDifferential (k : ℤ) (n : ℕ) :
    (cobarDifferential k (n + 1)).comp (cobarDifferential k n) = 0 := by
  have h := (cobarComplex k).d_comp_d n (n + 1) (n + 2)
  rw [cobarComplex_d, cobarComplex_d] at h
  exact congrArg AddCommGrpCat.Hom.hom h

/-! ### Low degrees: comparison with the structure maps of the Hopf algebroid -/

section LowDegree

variable {R : Type*} [CommRing R]

/-- In degree one, `Γ^{⊗1}` is the arrow ring `Γ` and the classification of `1`-simplices is
`arrowEquiv`. -/
theorem simplexEquiv_one_apply (k : CobarRing 1 →+* R) :
    simplexEquiv R 1 k = ((arrowEquiv R k).1, fun _ ↦ (arrowEquiv R k).2) := by
  rw [simplexEquiv_succ_apply, simplexEquiv_zero_apply, arrowEquiv_apply,
    includeLeft_eq_algebraMap, lastChange_eq_universalChange, Fin.snoc_zero]

/-- In degree two, `Γ^{⊗2}` is the ring `Γ ⊗_A Γ = Γ[u, u⁻¹, r, s, t]` of the coproduct: the
first arrow is classified by its left factor `algebraMap` and the second by its coordinates. -/
theorem simplexEquiv_two_apply (k : CobarRing 2 →+* R) :
    simplexEquiv R 2 k =
      (Universal.curve.map ((k.comp (algebraMap ArrowRing (ChangeRing ArrowRing))).comp
          (algebraMap (MvPolynomial Coeff ℤ) ArrowRing)),
        ![(ChangeRing.universalChange (MvPolynomial Coeff ℤ)).map
            (k.comp (algebraMap ArrowRing (ChangeRing ArrowRing))),
          (ChangeRing.universalChange ArrowRing).map k]) := by
  rw [simplexEquiv_succ_apply, simplexEquiv_one_apply, arrowEquiv_apply,
    includeLeft_eq_algebraMap, lastChange_eq_universalChange]
  refine Prod.ext rfl (funext fun i ↦ Fin.lastCases ?_ (fun j ↦ ?_) i) <;> dsimp only
  · rw [Fin.snoc_last]
    simp
  · rw [Fin.snoc_castSucc, Subsingleton.elim j 0, Fin.castSucc_zero, Matrix.cons_val_zero]

/-- The universal arrow `W → C • W` over `Γ`, as a `1`-simplex. -/
theorem universalSimplex_one :
    universalSimplex 1 =
      (Universal.curve.map (algebraMap (MvPolynomial Coeff ℤ) ArrowRing),
        fun _ ↦ ChangeRing.universalChange (MvPolynomial Coeff ℤ)) := by
  rw [universalSimplex, simplexEquiv_one_apply, arrowEquiv_apply, RingHom.id_comp,
    VariableChange.map_id]

/-- The coface `δ⁰ : A →+* Γ`, forgetting the source of an arrow, is the right unit `η_R`. -/
theorem cobarMap_succAbove_zero_eq_rightUnit :
    cobarMap (m := 0) (n := 1) (Fin.succAbove 0) = rightUnit := by
  refine (simplexEquiv _ 0).injective (Prod.ext ?_ (funext fun i ↦ i.elim0))
  rw [simplexEquiv_cobarMap, universalSimplex_one, simplexEquiv_zero_apply]
  simp only [nerveMap_fst, Fin.succAbove_zero, Fin.succ_zero_eq_one, vertexLabel_one]
  exact map_rightUnit.symm

/-- The coface `δ¹ : A →+* Γ`, forgetting the target of an arrow, is the left unit
`η_L = algebraMap`. -/
theorem cobarMap_succAbove_one_eq_algebraMap :
    cobarMap (m := 0) (n := 1) (Fin.succAbove 1) = algebraMap (MvPolynomial Coeff ℤ) ArrowRing := by
  refine (simplexEquiv _ 0).injective (Prod.ext ?_ (funext fun i ↦ i.elim0))
  rw [simplexEquiv_cobarMap, universalSimplex_one, simplexEquiv_zero_apply]
  simp

/-- The universal composable pair over `Γ ⊗_A Γ`: the first arrow comes from the left factor and
the second from the coordinates `u, r, s, t`. -/
theorem universalSimplex_two :
    universalSimplex 2 =
      (Universal.curve.map ((algebraMap ArrowRing (ChangeRing ArrowRing)).comp
          (algebraMap (MvPolynomial Coeff ℤ) ArrowRing)),
        ![(ChangeRing.universalChange (MvPolynomial Coeff ℤ)).map
            (algebraMap ArrowRing (ChangeRing ArrowRing)),
          ChangeRing.universalChange ArrowRing]) := by
  rw [universalSimplex, simplexEquiv_two_apply, RingHom.id_comp, VariableChange.map_id]

/-- The coface `δ⁰ : Γ →+* Γ ⊗_A Γ`, keeping the second arrow of a composable pair, is the
inclusion `1 ⊗ id` of the right factor. -/
theorem cobarMap_succAbove_zero_eq_map_rightUnit :
    cobarMap (m := 1) (n := 2) (Fin.succAbove 0) = ChangeRing.map rightUnit := by
  refine (simplexEquiv _ 1).injective ?_
  rw [simplexEquiv_cobarMap, universalSimplex_two, simplexEquiv_one_apply, arrowEquiv_apply,
    ChangeRing.map_comp_algebraMap, ChangeRing.universalChange_map_map, map_comp_rightUnit]
  refine Prod.ext ?_ (funext fun j ↦ ?_)
  · simp
  · fin_cases j
    simp

/-- The coface `δ¹ : Γ →+* Γ ⊗_A Γ`, composing the two arrows of a composable pair, is the
coproduct `Δ`. -/
theorem cobarMap_succAbove_one_eq_coproduct :
    cobarMap (m := 1) (n := 2) (Fin.succAbove 1) = coproduct := by
  refine (simplexEquiv _ 1).injective ?_
  rw [simplexEquiv_cobarMap, universalSimplex_two, simplexEquiv_one_apply, arrowEquiv_apply,
    coproduct_comp_algebraMap, universalChange_map_coproduct]
  refine Prod.ext ?_ (funext fun j ↦ ?_)
  · simp
  · fin_cases j
    simp

/-- The coface `δ² : Γ →+* Γ ⊗_A Γ`, keeping the first arrow of a composable pair, is the
inclusion `id ⊗ 1 = algebraMap` of the left factor. -/
theorem cobarMap_succAbove_two_eq_algebraMap :
    cobarMap (m := 1) (n := 2) (Fin.succAbove 2) = algebraMap ArrowRing (ChangeRing ArrowRing) :=
  -- `2 : Fin 3` is `Fin.last 2`.
  (cobarMap_succAbove_last_eq_includeLeft 1).trans (includeLeft_eq_algebraMap 1)

end LowDegree

/-- **The cobar differential in degree zero** is `f ↦ uᵏ η_R(f) - η_L(f)`. -/
theorem cobarDifferential_zero_apply (k : ℤ) (f : MvPolynomial Coeff ℤ) :
    cobarDifferential k 0 f =
      ↑((ChangeRing.universalChange (MvPolynomial Coeff ℤ)).u ^ k) * rightUnit f -
        algebraMap (MvPolynomial Coeff ℤ) ArrowRing f := by
  rw [cobarDifferential_apply, Fin.sum_univ_two, cobarAddMap_apply, cobarAddMap_apply,
    cobarMap_succAbove_zero_eq_rightUnit, cobarMap_succAbove_one_eq_algebraMap,
    cobarWeight_eq_of_apply_zero_eq_one (by decide), universalSimplex_one,
    cobarWeight_eq_one_of_apply_zero_eq_zero (by decide)]
  simp [sub_eq_add_neg]

/-- **The cocycles of degree zero of weight `k` are the integral modular forms of weight `k`**:
`uᵏ η_R(f) = η_L(f)` exactly when `f(C • W) = u⁻ᵏ f(W)` for every change of variables. -/
theorem ker_cobarDifferential_zero (k : ℕ) :
    (cobarDifferential k 0).ker =
      (TauCeti.WeierstrassCurve.integralModularFormSubmodule k).toAddSubgroup := by
  ext f
  rw [AddMonoidHom.mem_ker, cobarDifferential_zero_apply, sub_eq_zero,
    Submodule.mem_toAddSubgroup, TauCeti.WeierstrassCurve.mem_integralModularFormSubmodule,
    isIntegralModularForm_iff_rightUnit]
  -- What remains is `uᵏ x = y ↔ x = u⁻ᵏ y` for the unit `u` of the universal change.
  generalize (ChangeRing.universalChange (MvPolynomial Coeff ℤ)).u = u, rightUnit f = x,
    algebraMap (MvPolynomial Coeff ℤ) ArrowRing f = y
  constructor <;> rintro rfl <;> simp [← mul_assoc, ← mul_pow]

/-- **The cobar differential in degree one** is the cobar differential of the Hopf algebroid with
coefficients in `ω^k`: `γ ↦ u₁ᵏ (1 ⊗ γ) - Δ(γ) + γ ⊗ 1`, where `u₁` is the scaling factor of the
first arrow. -/
theorem cobarDifferential_one_apply (k : ℤ) (γ : ArrowRing) :
    cobarDifferential k 1 γ =
      algebraMap ArrowRing (ChangeRing ArrowRing)
          ↑((ChangeRing.universalChange (MvPolynomial Coeff ℤ)).u ^ k) *
          ChangeRing.map rightUnit γ -
        coproduct γ + algebraMap ArrowRing (ChangeRing ArrowRing) γ := by
  rw [cobarDifferential_apply, Fin.sum_univ_three, cobarAddMap_apply, cobarAddMap_apply,
    cobarAddMap_apply, cobarMap_succAbove_zero_eq_map_rightUnit,
    cobarMap_succAbove_one_eq_coproduct, cobarMap_succAbove_two_eq_algebraMap,
    cobarWeight_eq_of_apply_zero_eq_one (by decide), universalSimplex_two,
    cobarWeight_eq_one_of_apply_zero_eq_zero (by decide),
    cobarWeight_eq_one_of_apply_zero_eq_zero (by decide)]
  simp [sub_eq_add_neg, ← map_zpow]

end TauCeti.WeierstrassHopfAlgebroid
