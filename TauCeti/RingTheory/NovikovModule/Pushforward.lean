/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovModule.MapOfMatrix
public import TauCeti.RingTheory.NovikovModule.MapRange

/-!
# Pushforward of completed combinations along maps of generators

Let `F : S → ℝ` and `F' : S' → ℝ` be potentials on two sets of generators, and `π : S → S'` a map
of generators preserving potentials, `F' (π s) = F s`. Together with a ring homomorphism
`ρ : R →+* R'` of coefficients, `π` pushes a completed combination forward by summing coefficients
along the fibres of `π`:

`(pushforward ρ π hπ a)(s') = ∑ᶠ s ∈ π ⁻¹' {s'}, ρ (a s)`.

All generators in a fibre have the potential of `s'`, so only finitely many of them carry a
nonzero coefficient, and the result is again finite above every potential threshold. No
finiteness of the fibres is needed. The fibrewise sum is the formula of Mathlib's pushforward of
functions with locally finite support, `Function.locallyFinsupp.map` in
`Mathlib/Topology/LocallyFinsupp/Pushforward.lean`, with the potential cutoffs in place of a
topology. The pushforward is the coefficient change `TauCeti.NovikovModule.mapRange ρ` followed
by the kernel map `TauCeti.NovikovModule.kernelMap` of the graph kernel of `π`, with coefficient
`1` from `s` to `π s`. It is `ρ`-semilinear, sends the point mass `r`
at `s` to the point mass `ρ r` at `π s`, and extends the pushforward
`Finsupp.mapDomain π ∘ Finsupp.mapRange ρ` of finite combinations
(`TauCeti.NovikovModule.pushforward_ofFinsupp`). It keeps every potential cutoff, hence is
continuous; it is therefore the unique continuous extension of the pushforward of finite
combinations, and it satisfies the identity and composition laws. Along the identity of
generators it is the coefficient change `TauCeti.NovikovModule.mapRange`.

When the generators are finite unions of torsors, `S = Σ i, P i` under `H` and `S' = Σ i, P' i`
under `H'`, and `π` is equivariant along a homomorphism `φ : H →+ H'`, the pushforward is the
pushforward of Novikov series `TauCeti.NovikovSeries.map ρ φ` in each orbit, in the lift
coordinates of chosen lifts and of their images
(`TauCeti.NovikovModule.coordinates_pushforward`). Hence it is semilinear over
`TauCeti.NovikovSeries.mapRingHom ρ φ` for the Novikov module structures
(`TauCeti.NovikovModule.novikovPushforward`), and it carries the Novikov-linear map of a matrix
`M` of Novikov series to the map of the matrix obtained by applying
`TauCeti.NovikovSeries.mapRingHom` to the entries of `M`
(`TauCeti.NovikovModule.pushforward_novikovMapOfMatrix`). Thus identities between matrices of
Novikov series, such as `D * D = 0` for a differential or a chain homotopy equation, transport to
identities between the pushed-forward completed complexes. The main example is the action-field
specialization `TauCeti.NovikovModule.actionFieldMap`, in
`TauCeti.RingTheory.NovikovModule.ActionField`.

## Main definitions

* `TauCeti.NovikovModule.pushforward ρ π hπ`: the pushforward along a map of generators preserving
  potentials, as a `ρ`-semilinear map.
* `TauCeti.NovikovModule.novikovPushforward`: the same map on finite unions of torsors, as a
  semilinear map over the pushforward of Novikov rings.

## Main results

* `TauCeti.NovikovModule.pushforward_single`, `TauCeti.NovikovModule.pushforward_ofFinsupp`: the
  pushforward of point masses and of finite combinations.
* `TauCeti.NovikovModule.continuous_pushforward`: the pushforward is continuous.
* `TauCeti.NovikovModule.pushforward_pushforward`, `TauCeti.NovikovModule.pushforward_id`,
  `TauCeti.NovikovModule.pushforward_id_right`: functoriality, and the comparison with coefficient
  change.
* `TauCeti.NovikovModule.coordinates_pushforward`: the pushforward in lift coordinates.
* `TauCeti.NovikovModule.pushforward_novikovMapOfMatrix`: the pushforward of the map of a matrix.

## References

* M. Hutchings and Y.-J. Lee, *Circle-valued Morse theory and Reidemeister torsion*,
  Geom. Topol. 3 (1999), Section 2, on completed modules over Novikov rings.
* K. Fukaya, Y.-G. Oh, H. Ohta and K. Ono, *Lagrangian intersection Floer theory: anomaly and
  obstruction, Part I*, AMS/IP Studies in Advanced Mathematics 46.1, 2009, Section 5.1.
-/

public section

noncomputable section

open Function Set

namespace TauCeti

namespace NovikovModule

variable {R R' R'' S S' S'' : Type*}

section Semiring

variable [Semiring R] [Semiring R'] [Semiring R''] {F : S → ℝ} {F' : S' → ℝ} {F'' : S'' → ℝ}
  {π : S → S'} (hπ : ∀ s, F' (π s) = F s)

include hπ in
/-- The graph kernel of a potential-preserving map `π`, with coefficient `1` from `s` to `π s` and
`0` elsewhere, satisfies the potential bound with constant `0`. -/
private theorem potential_le_of_indicator_preimage_ne_zero (s : S) (s' : S')
    (h : (π ⁻¹' {s'}).indicator (1 : S → R') s ≠ 0) : F' s' ≤ F s + 0 := by
  have hs : π s = s' := mem_of_indicator_ne_zero h
  rw [add_zero, ← hπ s, hs]

/-- Each row of the graph kernel of a map of generators is a point mass, hence a completed
combination. -/
private theorem indicator_preimage_mem (s : S) :
    (fun s' => (π ⁻¹' {s'}).indicator (1 : S → R') s) ∈ NovikovModule R' F' :=
  mem_of_finite_support <| (finite_singleton (π s)).subset fun s' h =>
    (mem_of_indicator_ne_zero (mem_support.1 h) : π s = s').symm

/-- The **pushforward** of completed combinations along a coefficient map `ρ` and a map `π` of
generators preserving potentials: the coefficient at `s'` is the sum of the images under `ρ` of
the coefficients at the generators of the fibre of `π` over `s'`
(`TauCeti.NovikovModule.pushforward_apply_val`). It is the coefficient change
`TauCeti.NovikovModule.mapRange ρ` followed by the kernel map of the graph kernel of `π`. -/
def pushforward (ρ : R →+* R') (π : S → S') (hπ : ∀ s, F' (π s) = F s) :
    NovikovModule R F →ₛₗ[ρ] NovikovModule R' F' :=
  (kernelMap (potential_le_of_indicator_preimage_ne_zero (R' := R') hπ)
    indicator_preimage_mem).comp (mapRange ρ)

variable (ρ : R →+* R')

/-- The coefficient of a pushforward at `s'` is the sum of the images under `ρ` of the
coefficients in the fibre of `π` over `s'`. -/
theorem pushforward_apply_val (a : NovikovModule R F) (s' : S') :
    (pushforward ρ π hπ a).val s' = ∑ᶠ s ∈ π ⁻¹' {s'}, ρ (a.val s) := by
  rw [pushforward, LinearMap.comp_apply, kernelMap_apply_val, finsum_mem_def]
  exact finsum_congr fun s => by by_cases hs : s ∈ π ⁻¹' {s'} <;> simp [hs]

/-- A coefficient of a pushforward is the sum over any finite set of generators in the fibre
containing the generators of nonzero coefficient there. -/
theorem pushforward_apply_val_eq_sum (a : NovikovModule R F) {s' : S'} (t : Finset S)
    (ht : support a.val ∩ π ⁻¹' {s'} ⊆ t) (htπ : ∀ s ∈ t, π s = s') :
    (pushforward ρ π hπ a).val s' = ∑ s ∈ t, ρ (a.val s) := by
  rw [pushforward_apply_val]
  exact finsum_mem_eq_sum_of_subset _
    (fun s hs => ht ⟨fun h => hs.2 (by simp [h]), hs.1⟩) htπ

/-- Along an injective map of generators, the pushforward moves each coefficient to the image
generator. -/
@[simp]
theorem pushforward_apply_val_of_injective (hinj : Injective π) (a : NovikovModule R F) (s : S) :
    (pushforward ρ π hπ a).val (π s) = ρ (a.val s) := by
  classical
  rw [pushforward_apply_val_eq_sum hπ ρ a {s} (fun t ht => Finset.mem_singleton.2 (hinj ht.2))
    fun t ht => by rw [Finset.mem_singleton.1 ht], Finset.sum_singleton]

/-- A pushforward vanishes at generators outside the range of `π`. -/
theorem pushforward_apply_val_eq_zero_of_notMem_range (a : NovikovModule R F) {s' : S'}
    (hs' : s' ∉ range π) : (pushforward ρ π hπ a).val s' = 0 :=
  (pushforward_apply_val hπ ρ a s').trans <|
    finsum_mem_eq_zero_of_forall_eq_zero fun s hs => (hs' ⟨s, hs⟩).elim

/-- The pushforward of the point mass `r` at `s` is the point mass `ρ r` at `π s`. -/
@[simp]
theorem pushforward_single [DecidableEq S] [DecidableEq S'] (s : S) (r : R) :
    pushforward ρ π hπ (single s r) = single (π s) (ρ r) := by
  rw [pushforward, LinearMap.comp_apply, mapRange_single]
  refine Subtype.ext (funext fun s' => ?_)
  rw [kernelMap_single_apply_val, single_val]
  by_cases h : π s = s' <;> simp [h, Set.indicator]

/-- The pushforward extends the pushforward `Finsupp.mapDomain π ∘ Finsupp.mapRange ρ` of finite
combinations. -/
@[simp]
theorem pushforward_ofFinsupp (a : S →₀ R) :
    pushforward ρ π hπ (ofFinsupp F a) =
      ofFinsupp F' (Finsupp.mapDomain π (Finsupp.mapRange ρ (map_zero ρ) a)) := by
  classical
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
    rw [map_add, map_add, ha, hb, Finsupp.mapRange_add (map_add ρ), Finsupp.mapDomain_add,
      map_add]
  | single s r => simp

/-- Along the identity of generators, the pushforward is the coefficient change
`TauCeti.NovikovModule.mapRange`. -/
@[simp]
theorem pushforward_id_right : pushforward ρ id (fun _ : S => rfl) = mapRange (F := F) ρ :=
  LinearMap.ext fun a => Subtype.ext <| funext fun s => by
    rw [mapRange_apply_val]
    exact pushforward_apply_val_of_injective (π := id) (fun _ => rfl) ρ injective_id a s

/-- The pushforward along the identities of coefficients and of generators is the identity. -/
theorem pushforward_id :
    pushforward (RingHom.id R) id (fun _ : S => rfl) = LinearMap.id (M := NovikovModule R F) :=
  (pushforward_id_right (RingHom.id R)).trans <| LinearMap.ext mapRange_id

/-- **Functoriality.** Pushing forward along `π` and then along `π'` is pushing forward along
`π' ∘ π`, with the composite coefficient map. -/
@[simp]
theorem pushforward_pushforward {π' : S' → S''} (hπ' : ∀ s', F'' (π' s') = F' s') (ρ' : R' →+* R'')
    (a : NovikovModule R F) :
    pushforward ρ' π' hπ' (pushforward ρ π hπ a) =
      pushforward (ρ'.comp ρ) (π' ∘ π) (fun s => (hπ' (π s)).trans (hπ s)) a := by
  have hk : kernelComp (fun s s' => ρ' ((π ⁻¹' {s'}).indicator (1 : S → R') s))
      (fun s' s'' => (π' ⁻¹' {s''}).indicator (1 : S' → R'') s') =
      fun s s'' => ((π' ∘ π) ⁻¹' {s''}).indicator 1 s := by
    ext s s''
    rw [kernelComp_apply, finsum_eq_single _ (π s) fun s' hs' => by simp [Ne.symm hs']]
    by_cases h : π' (π s) = s'' <;> simp [h]
  have hm (s : S) (s' : S') (h : ρ' ((π ⁻¹' {s'}).indicator (1 : S → R') s) ≠ 0) :
      F' s' ≤ F s + 0 :=
    potential_le_of_indicator_preimage_ne_zero hπ s s' fun h' => h (by rw [h', map_zero])
  rw [pushforward, pushforward, pushforward, LinearMap.comp_apply, LinearMap.comp_apply,
    mapRange_kernelMap ρ' _ _ hm fun s => comp_mem (map_zero ρ') (indicator_preimage_mem s),
    LinearMap.comp_apply, mapRange_mapRange]
  refine (kernelMap_kernelMap (C'' := 0 + 0) _ _ _ _
    (fun s s'' h => (potential_le_of_kernelComp_ne_zero (D := F s + 0) (hm s)
      (potential_le_of_indicator_preimage_ne_zero hπ' · s'') h).trans_eq (add_assoc _ _ _))
    (fun s => kernelComp_mem (potential_le_of_indicator_preimage_ne_zero hπ')
      indicator_preimage_mem (comp_mem (map_zero ρ') (indicator_preimage_mem s))) _).trans ?_
  exact LinearMap.congr_fun ((kernelMap_inj _ _ _ _).2 hk) _

end Semiring

section Ring

variable [Ring R] [Ring R'] {F : S → ℝ} {F' : S' → ℝ}
  {π : S → S'} (hπ : ∀ s, F' (π s) = F s) (ρ : R →+* R')

/-- The pushforward keeps every potential cutoff: a combination vanishing above `C` is sent to a
combination vanishing above `C`. -/
theorem pushforward_mem_potentialFiltration {C : ℝ} {a : NovikovModule R F}
    (ha : a ∈ potentialFiltration R F C) : pushforward ρ π hπ a ∈ potentialFiltration R' F' C :=
  add_zero C ▸ kernelMap_mem_potentialFiltration _ _ (mapRange_mem_potentialFiltration ρ ha)

/-- The pushforward is continuous for the potential-cutoff topologies. -/
@[fun_prop]
theorem continuous_pushforward : Continuous (pushforward ρ π hπ) :=
  (continuous_kernelMap _ _).comp (continuous_mapRange ρ)

end Ring

section Coordinates

variable [Semiring R] [Semiring R'] {H H' ι : Type*} [AddGroup H] [AddGroup H'] [Finite ι]
  {P P' : ι → Type*} [∀ i, AddTorsor H (P i)] [∀ i, AddTorsor H' (P' i)] {N : H →+ ℝ}
  {N' : H' →+ ℝ} {F : (Σ i, P i) → ℝ} {F' : (Σ i, P' i) → ℝ}
  (hF : ∀ i h (p : P i), F ⟨i, h +ᵥ p⟩ = F ⟨i, p⟩ - N h)
  (hF' : ∀ i h (p : P' i), F' ⟨i, h +ᵥ p⟩ = F' ⟨i, p⟩ - N' h)
  (ρ : R →+* R') {φ : H →+ H'} (hφ : ∃ c > 0, ∀ h, N' (φ h) = c * N h) {π : ∀ i, P i → P' i}
  (hπφ : ∀ i h (p : P i), π i (h +ᵥ p) = φ h +ᵥ π i p)
  (hπ : ∀ s : Σ i, P i, F' (Sigma.map id π s) = F s)

include hF hF' hπφ in
/-- **The pushforward in lift coordinates.** If `π` is equivariant along `φ`, the coordinates of
the pushforward relative to the images of the lifts `r` are the pushforwards of Novikov series
along `ρ` and `φ` of the coordinates relative to `r`. -/
theorem coordinates_pushforward (r : ∀ i, P i) (a : NovikovModule R F) (i : ι) :
    coordinates hF' (fun i => π i (r i)) (pushforward ρ (Sigma.map id π) hπ a) i =
      NovikovSeries.mapRingHom ρ φ hφ (coordinates hF r a i) := by
  ext h'
  rw [coordinates_coeff, pushforward_apply_val, NovikovSeries.mapRingHom_apply,
    NovikovSeries.coeff_map]
  have hfib : Sigma.map id π ⁻¹' {⟨i, h' +ᵥ π i (r i)⟩} =
      (fun h : H => (⟨i, h +ᵥ r i⟩ : Σ i, P i)) '' (φ ⁻¹' {h'}) := by
    ext ⟨j, p⟩
    simp only [mem_preimage, mem_singleton_iff, Sigma.map, id_eq, mem_image]
    constructor
    · intro hp
      obtain rfl : j = i := congrArg Sigma.fst hp
      have hp' : π j p = h' +ᵥ π j (r j) := eq_of_heq (Sigma.mk.inj_iff.1 hp).2
      refine ⟨p -ᵥ r j, ?_, by rw [vsub_vadd]⟩
      rw [← vsub_vadd p (r j), hπφ] at hp'
      exact vadd_right_cancel _ hp'
    · rintro ⟨h, hh, hp⟩
      obtain ⟨rfl, hp⟩ := Sigma.mk.inj_iff.1 hp
      obtain rfl := eq_of_heq hp
      rw [hπφ, mem_singleton_iff.1 (mem_preimage.1 hh)]
  rw [hfib, finsum_mem_image fun h _ k _ hk =>
    vadd_right_cancel _ (eq_of_heq (Sigma.mk.inj_iff.1 hk).2)]
  simp only [coordinates_coeff, AddMonoidHom.coe_ofClass]

include hF hF' hπφ in
/-- The pushforward is semilinear for the Novikov module structures of
`TauCeti.NovikovModule.module`, over the pushforward `TauCeti.NovikovSeries.mapRingHom ρ φ` of
Novikov rings. -/
theorem pushforward_smul (β : NovikovSeries R H N)
    (a : NovikovModule R F) :
    letI := module (R := R) hF
    letI := module (R := R') hF'
    pushforward ρ (Sigma.map id π) hπ (β • a) =
      NovikovSeries.mapRingHom ρ φ hφ β • pushforward ρ (Sigma.map id π) hπ a := by
  let := module (R := R) hF
  let := module (R := R') hF'
  let r := fun i => Classical.arbitrary (P i)
  refine (coordinates hF' fun i => π i (r i)).injective (funext fun i => ?_)
  simp only [coordinates_pushforward hF hF' ρ hφ hπφ hπ, coordinates_smul, Pi.smul_apply,
    smul_eq_mul, map_mul]

include hF hF' hπφ in
/-- The pushforward on finite unions of torsors, as a semilinear map over the pushforward
`TauCeti.NovikovSeries.mapRingHom ρ φ` of Novikov rings, for the Novikov module structures of
`TauCeti.NovikovModule.module`. -/
def novikovPushforward :
    letI := module (R := R) hF
    letI := module (R := R') hF'
    NovikovModule R F →ₛₗ[NovikovSeries.mapRingHom ρ φ hφ] NovikovModule R' F' :=
  letI := module (R := R) hF
  letI := module (R := R') hF'
  { toFun := pushforward ρ (Sigma.map id π) hπ
    map_add' := map_add _
    map_smul' := pushforward_smul hF hF' ρ hφ hπφ hπ }

/-- The Novikov-semilinear pushforward evaluates to the pushforward. -/
@[simp]
theorem novikovPushforward_apply (a : NovikovModule R F) :
    novikovPushforward hF hF' ρ hφ hπφ hπ a = pushforward ρ (Sigma.map id π) hπ a :=
  (rfl)

end Coordinates

section Matrix

variable [CommSemiring R] [CommSemiring R'] {H H' ι₁ ι₀ : Type*} [AddCommGroup H]
  [AddCommGroup H'] [Finite ι₁] [Finite ι₀] {P₁ P₁' : ι₁ → Type*} {P₀ P₀' : ι₀ → Type*}
  [∀ i, AddTorsor H (P₁ i)] [∀ i, AddTorsor H' (P₁' i)] [∀ k, AddTorsor H (P₀ k)]
  [∀ k, AddTorsor H' (P₀' k)] {N : H →+ ℝ} {N' : H' →+ ℝ} {F₁ : (Σ i, P₁ i) → ℝ}
  {F₁' : (Σ i, P₁' i) → ℝ} {F₀ : (Σ k, P₀ k) → ℝ} {F₀' : (Σ k, P₀' k) → ℝ}
  (hF₁ : ∀ i h (p : P₁ i), F₁ ⟨i, h +ᵥ p⟩ = F₁ ⟨i, p⟩ - N h)
  (hF₁' : ∀ i h (p : P₁' i), F₁' ⟨i, h +ᵥ p⟩ = F₁' ⟨i, p⟩ - N' h)
  (hF₀ : ∀ k h (p : P₀ k), F₀ ⟨k, h +ᵥ p⟩ = F₀ ⟨k, p⟩ - N h)
  (hF₀' : ∀ k h (p : P₀' k), F₀' ⟨k, h +ᵥ p⟩ = F₀' ⟨k, p⟩ - N' h)
  (ρ : R →+* R') {φ : H →+ H'} (hφ : ∃ c > 0, ∀ h, N' (φ h) = c * N h)
  {π₁ : ∀ i, P₁ i → P₁' i} {π₀ : ∀ k, P₀ k → P₀' k}
  (hπφ₁ : ∀ i h (p : P₁ i), π₁ i (h +ᵥ p) = φ h +ᵥ π₁ i p)
  (hπφ₀ : ∀ k h (p : P₀ k), π₀ k (h +ᵥ p) = φ h +ᵥ π₀ k p)
  (hπ₁ : ∀ s : Σ i, P₁ i, F₁' (Sigma.map id π₁ s) = F₁ s)
  (hπ₀ : ∀ s : Σ k, P₀ k, F₀' (Sigma.map id π₀ s) = F₀ s)

include hπφ₁ hπφ₀ in
/-- **Pushforward of the map of a matrix.** The pushforward carries the Novikov-linear map of a
matrix `M` of Novikov series, relative to reference lifts `r₁` and `r₀`, to the map of the matrix
obtained by applying `TauCeti.NovikovSeries.mapRingHom ρ φ` to every entry of `M`, relative to the
image lifts. -/
theorem pushforward_novikovMapOfMatrix (r₁ : ∀ i, P₁ i) (r₀ : ∀ k, P₀ k)
    (M : Matrix ι₁ ι₀ (NovikovSeries R H N)) (a : NovikovModule R F₁) :
    pushforward ρ (Sigma.map id π₀) hπ₀ (novikovMapOfMatrix hF₁ hF₀ r₁ r₀ M a) =
      novikovMapOfMatrix hF₁' hF₀' (fun i => π₁ i (r₁ i)) (fun k => π₀ k (r₀ k))
        (M.map (NovikovSeries.mapRingHom ρ φ hφ)) (pushforward ρ (Sigma.map id π₁) hπ₁ a) := by
  have := Fintype.ofFinite ι₁
  refine (coordinates hF₀' fun k => π₀ k (r₀ k)).injective (funext fun k => ?_)
  rw [coordinates_pushforward hF₀ hF₀' ρ hφ hπφ₀ hπ₀, coordinates_novikovMapOfMatrix,
    coordinates_novikovMapOfMatrix, map_sum]
  simp only [map_mul, Matrix.map_apply, coordinates_pushforward hF₁ hF₁' ρ hφ hπφ₁ hπ₁]

end Matrix

end NovikovModule

end TauCeti
