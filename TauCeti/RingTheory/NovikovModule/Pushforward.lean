/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovModule.MapOfMatrix
public import TauCeti.RingTheory.NovikovModule.MapRange
public import TauCeti.RingTheory.NovikovSeries.ActionField

/-!
# Pushforward of completed combinations along maps of generators

Let `F : S → ℝ` and `F' : S' → ℝ` be potentials on two sets of generators, and `π : S → S'` a map
of generators preserving potentials, `F' (π s) = F s`. Together with a ring homomorphism
`ρ : R →+* R'` of coefficients, `π` pushes a completed combination forward by summing coefficients
along the fibres of `π`:

`(map ρ π hπ a)(s') = ∑ᶠ s ∈ π ⁻¹' {s'}, ρ (a s)`.

All generators in a fibre have the potential of `s'`, so only finitely many of them carry a
nonzero coefficient, and the result is again finite above every potential threshold. No
finiteness of the fibres is needed. The fibrewise sum is the formula of Mathlib's pushforward of
functions with locally finite support, `Function.locallyFinsupp.map` in
`Mathlib/Topology/LocallyFinsupp/Pushforward.lean`, with the potential cutoffs in place of a
topology. The pushforward is `ρ`-semilinear, sends the point mass `r`
at `s` to the point mass `ρ r` at `π s`, and extends the pushforward
`Finsupp.mapDomain π ∘ Finsupp.mapRange ρ` of finite combinations
(`TauCeti.NovikovModule.map_ofFinsupp`). It keeps every potential cutoff, hence is continuous; it
is therefore the unique continuous extension of the pushforward of finite combinations, and it
satisfies the identity and composition laws. Along the identity of generators it is the
coefficient change `TauCeti.NovikovModule.mapRange`.

When the generators are finite unions of torsors, `S = Σ i, P i` under `H` and `S' = Σ i, P' i`
under `H'`, and `π` is equivariant along a homomorphism `φ : H →+ H'`, the pushforward is the
pushforward of Novikov series `TauCeti.NovikovSeries.map ρ φ` in each orbit, in the lift
coordinates of chosen lifts and of their images (`TauCeti.NovikovModule.coordinates_map`). Hence
it is semilinear over `TauCeti.NovikovSeries.mapRingHom ρ φ` for the Novikov module structures
(`TauCeti.NovikovModule.novikovMap`), and it carries the Novikov-linear map of a matrix `M` of
Novikov series to the map of the matrix obtained by applying `TauCeti.NovikovSeries.mapRingHom`
to the entries of `M` (`TauCeti.NovikovModule.map_novikovMapOfMatrix`). Thus identities between
matrices of Novikov series, such as `D * D = 0` for a differential or a chain homotopy equation,
transport to identities between the pushed-forward completed complexes.

The main example is the *action-field specialization*. For torsors under the action-weighted
exponent group `G × ℝ`, with period `E_R (g, r) = E g + r`, chosen lifts `r i` identify each orbit
with a copy of `ℝ` through `p ↦ E_R (p -ᵥ r i)`, and the pushforward along these maps
(`TauCeti.NovikovModule.actionFieldMap`) is a completed combination over the field-valued Novikov
series `Nov(k, ℝ, id)`, with one generator for each energy in each orbit. Its coordinates are the
images of the coordinates under the action-field map of Novikov series
(`TauCeti.NovikovModule.coordinates_actionFieldMap`), and matrices go to their entrywise
images (`TauCeti.NovikovModule.actionFieldMap_novikovMapOfMatrix`). This specializes a finite
Floer complex over the action-weighted Novikov ring to a finite complex over the Novikov field.

## Main definitions

* `TauCeti.NovikovModule.map ρ π hπ`: the pushforward along a map of generators preserving
  potentials, as a `ρ`-semilinear map.
* `TauCeti.NovikovModule.novikovMap`: the same map on finite unions of torsors, as a semilinear
  map over the pushforward of Novikov rings.
* `TauCeti.NovikovModule.actionFieldMap`: the action-field specialization of completed
  combinations on torsors under the action-weighted exponent group.

## Main results

* `TauCeti.NovikovModule.map_single`, `TauCeti.NovikovModule.map_ofFinsupp`: the pushforward of
  point masses and of finite combinations.
* `TauCeti.NovikovModule.continuous_map`: the pushforward is continuous.
* `TauCeti.NovikovModule.map_map`, `TauCeti.NovikovModule.map_id`,
  `TauCeti.NovikovModule.map_id_right`: functoriality, and the comparison with coefficient change.
* `TauCeti.NovikovModule.coordinates_map`: the pushforward in lift coordinates.
* `TauCeti.NovikovModule.map_novikovMapOfMatrix`: the pushforward of the map of a matrix.

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
/-- All generators in a fibre of a potential-preserving map have the same potential, so a
completed combination has only finitely many nonzero coefficients in each fibre. -/
theorem finite_support_inter_preimage_singleton (a : NovikovModule R F) (s' : S') :
    (support a.val ∩ π ⁻¹' {s'}).Finite :=
  (finite_ge a (F' s')).subset fun s hs => ⟨hs.1, by
    rw [← hπ s, show π s = s' from hs.2]⟩

include hπ in
/-- Summing the coefficients of a completed combination along the fibres of a potential-preserving
map gives a completed combination. -/
private theorem finsum_mem_preimage_singleton_mem (ρ : R →+* R') (a : NovikovModule R F) :
    (fun s' => ∑ᶠ s ∈ π ⁻¹' {s'}, ρ (a.val s)) ∈ NovikovModule R' F' := mem_iff.2 fun C =>
  ((finite_gt a C).image π).subset fun s' hs' => by
    obtain ⟨s, hs, hρ⟩ := exists_ne_zero_of_finsum_mem_ne_zero hs'.1
    refine ⟨s, ⟨fun h => hρ (by rw [h, map_zero]), ?_⟩, hs⟩
    rw [← hπ s, show π s = s' from hs]
    exact hs'.2

/-- A sum along a fibre is the sum over any finite set of generators in the fibre containing those
of nonzero coefficient. -/
private theorem finsum_mem_preimage_singleton_eq_sum (ρ : R →+* R') (a : NovikovModule R F)
    {s' : S'} (t : Finset S) (ht : support a.val ∩ π ⁻¹' {s'} ⊆ t)
    (htπ : ∀ s ∈ t, π s = s') :
    ∑ᶠ s ∈ π ⁻¹' {s'}, ρ (a.val s) = ∑ s ∈ t, ρ (a.val s) :=
  finsum_mem_eq_sum_of_subset _ (fun s hs => ht ⟨fun h => hs.2 (by simp [h]), hs.1⟩) htπ

/-- The **pushforward** of completed combinations along a coefficient map `ρ` and a map `π` of
generators preserving potentials: the coefficient at `s'` is the sum of the images under `ρ` of
the coefficients at the generators of the fibre of `π` over `s'`. -/
def map (ρ : R →+* R') (π : S → S') (hπ : ∀ s, F' (π s) = F s) :
    NovikovModule R F →ₛₗ[ρ] NovikovModule R' F' where
  toFun a := ⟨fun s' => ∑ᶠ s ∈ π ⁻¹' {s'}, ρ (a.val s), finsum_mem_preimage_singleton_mem hπ ρ a⟩
  map_add' a b := Subtype.ext <| funext fun s' => by
    simp only [Submodule.coe_add, Pi.add_apply, map_add]
    exact finsum_mem_add_distrib'
      ((finite_support_inter_preimage_singleton hπ a s').subset fun s hs =>
        ⟨fun h => hs.2 (by simp [h]), hs.1⟩)
      ((finite_support_inter_preimage_singleton hπ b s').subset fun s hs =>
        ⟨fun h => hs.2 (by simp [h]), hs.1⟩)
  map_smul' c a := Subtype.ext <| funext fun s' => by
    classical
    have hfin := finite_support_inter_preimage_singleton hπ a s'
    have ht (s : S) (hs : s ∈ hfin.toFinset) : π s = s' := ((Finite.mem_toFinset _).1 hs).2
    simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, map_mul]
    rw [finsum_mem_preimage_singleton_eq_sum (π := π) ρ a hfin.toFinset
      (fun s hs => (Finite.mem_toFinset _).2 hs) ht, Finset.mul_sum]
    exact finsum_mem_eq_sum_of_subset _
      (fun s hs => (Finite.mem_toFinset _).2 ⟨fun h => hs.2 (by simp [h]), hs.1⟩) ht

variable (ρ : R →+* R')

/-- The coefficient of a pushforward at `s'` is the sum of the images under `ρ` of the
coefficients in the fibre of `π` over `s'`. -/
theorem map_apply_val (a : NovikovModule R F) (s' : S') :
    (map ρ π hπ a).val s' = ∑ᶠ s ∈ π ⁻¹' {s'}, ρ (a.val s) :=
  (rfl)

/-- A coefficient of a pushforward is the sum over any finite set of generators in the fibre
containing the generators of nonzero coefficient there. -/
theorem map_apply_val_eq_sum (a : NovikovModule R F) {s' : S'} (t : Finset S)
    (ht : support a.val ∩ π ⁻¹' {s'} ⊆ t) (htπ : ∀ s ∈ t, π s = s') :
    (map ρ π hπ a).val s' = ∑ s ∈ t, ρ (a.val s) :=
  finsum_mem_preimage_singleton_eq_sum ρ a t ht htπ

/-- Along an injective map of generators, the pushforward moves each coefficient to the image
generator. -/
@[simp]
theorem map_apply_val_of_injective (hinj : Injective π) (a : NovikovModule R F) (s : S) :
    (map ρ π hπ a).val (π s) = ρ (a.val s) := by
  classical
  rw [map_apply_val_eq_sum hπ ρ a {s} (fun t ht => Finset.mem_singleton.2 (hinj ht.2))
    fun t ht => by rw [Finset.mem_singleton.1 ht], Finset.sum_singleton]

/-- A pushforward vanishes at generators outside the range of `π`. -/
theorem map_apply_val_eq_zero_of_notMem_range (a : NovikovModule R F) {s' : S'}
    (hs' : s' ∉ range π) : (map ρ π hπ a).val s' = 0 :=
  finsum_mem_eq_zero_of_forall_eq_zero fun s hs => (hs' ⟨s, hs⟩).elim

/-- The pushforward of the point mass `r` at `s` is the point mass `ρ r` at `π s`. -/
@[simp]
theorem map_single [DecidableEq S] [DecidableEq S'] (s : S) (r : R) :
    map ρ π hπ (single s r) = single (π s) (ρ r) := by
  refine Subtype.ext (funext fun s' => ?_)
  rw [map_apply_val_eq_sum hπ ρ _ (if π s = s' then {s} else ∅)]
  · split_ifs with h
    · subst h
      simp
    · simp [Pi.single_apply, Ne.symm h]
  · rintro t ⟨ht, rfl⟩
    have : t = s := by
      by_contra hts
      exact ht (by simp [hts])
    subst this
    simp
  · intro t ht
    split_ifs at ht with h
    · rw [Finset.mem_singleton.1 ht, h]
    · simp at ht

/-- The pushforward extends the pushforward `Finsupp.mapDomain π ∘ Finsupp.mapRange ρ` of finite
combinations. -/
@[simp]
theorem map_ofFinsupp (a : S →₀ R) :
    map ρ π hπ (ofFinsupp F a) =
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
theorem map_id_right : map ρ id (fun _ : S => rfl) = mapRange (F := F) ρ :=
  LinearMap.ext fun a => Subtype.ext <| funext fun s => by
    rw [mapRange_apply_val]
    exact map_apply_val_of_injective (π := id) (fun _ => rfl) ρ injective_id a s

/-- The pushforward along the identities of coefficients and of generators is the identity. -/
@[simp]
theorem map_id : map (RingHom.id R) id (fun _ : S => rfl) = LinearMap.id (M := NovikovModule R F) :=
  (map_id_right (RingHom.id R)).trans <| LinearMap.ext mapRange_id

end Semiring

section Ring

variable [Ring R] [Ring R'] [Ring R''] {F : S → ℝ} {F' : S' → ℝ} {F'' : S'' → ℝ}
  {π : S → S'} (hπ : ∀ s, F' (π s) = F s) (ρ : R →+* R')

/-- The pushforward keeps every potential cutoff: a combination vanishing above `C` is sent to a
combination vanishing above `C`. -/
theorem map_mem_potentialFiltration {C : ℝ} {a : NovikovModule R F}
    (ha : a ∈ potentialFiltration R F C) : map ρ π hπ a ∈ potentialFiltration R' F' C :=
  mem_potentialFiltration.2 fun s' hs' => finsum_mem_eq_zero_of_forall_eq_zero fun s hs => by
    rw [mem_potentialFiltration.1 ha s (by rwa [← hπ s, show π s = s' from hs]), map_zero]

/-- The pushforward is continuous for the potential-cutoff topologies. -/
theorem continuous_map : Continuous (map ρ π hπ) :=
  continuous_of_forall_mem_potentialFiltration (map ρ π hπ) fun C =>
    ⟨C, fun _ ha => map_mem_potentialFiltration hπ ρ ha⟩

/-- **Functoriality.** Pushing forward along `π` and then along `π'` is pushing forward along
`π' ∘ π`, with the composite coefficient map. -/
theorem map_map {π' : S' → S''} (hπ' : ∀ s', F'' (π' s') = F' s') (ρ' : R' →+* R'')
    (a : NovikovModule R F) :
    map ρ' π' hπ' (map ρ π hπ a) =
      map (ρ'.comp ρ) (π' ∘ π) (fun s => (hπ' (π s)).trans (hπ s)) a := by
  classical
  have h := addHom_ext (f := (map ρ' π' hπ').toAddMonoidHom.comp (map ρ π hπ).toAddMonoidHom)
    (g := (map (ρ'.comp ρ) (π' ∘ π) (fun s => (hπ' (π s)).trans (hπ s))).toAddMonoidHom)
    ((continuous_map hπ' ρ').comp (continuous_map hπ ρ))
    (continuous_map (fun s => (hπ' (π s)).trans (hπ s)) (ρ'.comp ρ)) fun s r => by
      simp
  exact DFunLike.congr_fun h a

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
theorem coordinates_map (r : ∀ i, P i) (a : NovikovModule R F) (i : ι) :
    coordinates hF' (fun i => π i (r i)) (map ρ (Sigma.map id π) hπ a) i =
      NovikovSeries.mapRingHom ρ φ hφ (coordinates hF r a i) := by
  ext h'
  rw [coordinates_coeff, map_apply_val, NovikovSeries.mapRingHom_apply, NovikovSeries.coeff_map]
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
      rw [hπφ, show φ h = h' from hh]
  rw [hfib, finsum_mem_image fun h _ k _ hk =>
    vadd_right_cancel _ (eq_of_heq (Sigma.mk.inj_iff.1 hk).2)]
  simp only [coordinates_coeff, AddMonoidHom.coe_ofClass]

include hF hF' hπφ in
/-- The pushforward is semilinear for the Novikov module structures of
`TauCeti.NovikovModule.module`, over the pushforward `TauCeti.NovikovSeries.mapRingHom ρ φ` of
Novikov rings. -/
theorem map_smul_novikov (β : NovikovSeries R H N)
    (a : NovikovModule R F) :
    letI := module (R := R) hF
    letI := module (R := R') hF'
    map ρ (Sigma.map id π) hπ (β • a) =
      NovikovSeries.mapRingHom ρ φ hφ β • map ρ (Sigma.map id π) hπ a := by
  let := module (R := R) hF
  let := module (R := R') hF'
  let r := fun i => Classical.arbitrary (P i)
  refine (coordinates hF' fun i => π i (r i)).injective (funext fun i => ?_)
  simp only [coordinates_map hF hF' ρ hφ hπφ hπ, coordinates_smul, Pi.smul_apply, smul_eq_mul,
    map_mul]

include hF hF' hπφ in
/-- The pushforward on finite unions of torsors, as a semilinear map over the pushforward
`TauCeti.NovikovSeries.mapRingHom ρ φ` of Novikov rings, for the Novikov module structures of
`TauCeti.NovikovModule.module`. -/
def novikovMap :
    letI := module (R := R) hF
    letI := module (R := R') hF'
    NovikovModule R F →ₛₗ[NovikovSeries.mapRingHom ρ φ hφ] NovikovModule R' F' :=
  letI := module (R := R) hF
  letI := module (R := R') hF'
  { toFun := map ρ (Sigma.map id π) hπ
    map_add' := map_add _
    map_smul' := map_smul_novikov hF hF' ρ hφ hπφ hπ }

/-- The Novikov-semilinear pushforward evaluates to the pushforward. -/
@[simp]
theorem novikovMap_apply (a : NovikovModule R F) :
    novikovMap hF hF' ρ hφ hπφ hπ a = map ρ (Sigma.map id π) hπ a :=
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
theorem map_novikovMapOfMatrix (r₁ : ∀ i, P₁ i) (r₀ : ∀ k, P₀ k)
    (M : Matrix ι₁ ι₀ (NovikovSeries R H N)) (a : NovikovModule R F₁) :
    map ρ (Sigma.map id π₀) hπ₀ (novikovMapOfMatrix hF₁ hF₀ r₁ r₀ M a) =
      novikovMapOfMatrix hF₁' hF₀' (fun i => π₁ i (r₁ i)) (fun k => π₀ k (r₀ k))
        (M.map (NovikovSeries.mapRingHom ρ φ hφ)) (map ρ (Sigma.map id π₁) hπ₁ a) := by
  have := Fintype.ofFinite ι₁
  refine (coordinates hF₀' fun k => π₀ k (r₀ k)).injective (funext fun k => ?_)
  rw [coordinates_map hF₀ hF₀' ρ hφ hπφ₀ hπ₀, coordinates_novikovMapOfMatrix,
    coordinates_novikovMapOfMatrix, map_sum]
  simp only [map_mul, Matrix.map_apply, coordinates_map hF₁ hF₁' ρ hφ hπφ₁ hπ₁]

end Matrix

section ActionField

variable {k G ι ι₀ : Type*} [AddCommGroup G] {E : G →+ ℝ} {P : ι → Type*} {P₀ : ι₀ → Type*}
  [∀ i, AddTorsor (G × ℝ) (P i)] [∀ k, AddTorsor (G × ℝ) (P₀ k)] {F : (Σ i, P i) → ℝ}
  {F₀ : (Σ k, P₀ k) → ℝ}
  (hF : ∀ i h (p : P i), F ⟨i, h +ᵥ p⟩ = F ⟨i, p⟩ - E.coprod (AddMonoidHom.id ℝ) h)
  (hF₀ : ∀ k h (p : P₀ k), F₀ ⟨k, h +ᵥ p⟩ = F₀ ⟨k, p⟩ - E.coprod (AddMonoidHom.id ℝ) h)

variable (F) in
/-- The potential of the action-field generators `Σ _ : ι, ℝ` for the lifts `r`: the energy `t` in
the orbit `i` has the potential `F (r i) - t`. -/
def actionFieldPotential (r : ∀ i, P i) (s : Σ _ : ι, ℝ) : ℝ :=
  F ⟨s.1, r s.1⟩ - s.2

@[simp]
theorem actionFieldPotential_apply (r : ∀ i, P i) (s : Σ _ : ι, ℝ) :
    actionFieldPotential F r s = F ⟨s.1, r s.1⟩ - s.2 :=
  (rfl)

variable (F) in
/-- On the action-field generators, translating the energy by `t` lowers the potential by `t`:
each orbit is a torsor under `ℝ` with the identity period. -/
theorem actionFieldPotential_vadd (r : ∀ i, P i) (i : ι) (t x : ℝ) :
    actionFieldPotential F r ⟨i, t +ᵥ x⟩ =
      actionFieldPotential F r ⟨i, x⟩ - AddMonoidHom.id ℝ t := by
  simp only [actionFieldPotential_apply, vadd_eq_add, AddMonoidHom.id_apply]
  ring

/-- The energy `E_R (p -ᵥ r i)` of a generator relative to the lift of its orbit. -/
private theorem vadd_vsub_energy (r : ∀ i, P i) (i : ι) (h : G × ℝ) (p : P i) :
    E.coprod (AddMonoidHom.id ℝ) ((h +ᵥ p) -ᵥ r i) =
      E.coprod (AddMonoidHom.id ℝ) h +ᵥ E.coprod (AddMonoidHom.id ℝ) (p -ᵥ r i) := by
  rw [vadd_vsub_assoc, map_add, vadd_eq_add]

include hF in
/-- The energy map `p ↦ E_R (p -ᵥ r i)` of each orbit preserves potentials. -/
theorem actionFieldPotential_energy (r : ∀ i, P i) (s : Σ i, P i) :
    actionFieldPotential F r
        (Sigma.map id (fun i p => E.coprod (AddMonoidHom.id ℝ) (p -ᵥ r i)) s) = F s := by
  obtain ⟨i, p⟩ := s
  rw [Sigma.map_mk, actionFieldPotential_apply, potential_eq_sub_vsub hF r i p, id_eq]

section Semiring

variable [Semiring R] [Semiring k] (ρ : R →+* k)

/-- The **action-field specialization** of completed combinations on torsors under the
action-weighted exponent group `G × ℝ`: the pushforward along the coefficient map `ρ` and the
energy maps `p ↦ E_R (p -ᵥ r i)` from each orbit to `ℝ`, relative to lifts `r`. Its values are
completed combinations of the generators `Σ _ : ι, ℝ` with the potential
`TauCeti.NovikovModule.actionFieldPotential F r`. -/
def actionFieldMap (r : ∀ i, P i) :
    NovikovModule R F →ₛₗ[ρ] NovikovModule k (actionFieldPotential F r) :=
  map ρ (Sigma.map id fun i p => E.coprod (AddMonoidHom.id ℝ) (p -ᵥ r i))
    (actionFieldPotential_energy hF r)

/-- The action-field specialization is the pushforward along the energy maps of the orbits. -/
theorem actionFieldMap_apply (r : ∀ i, P i) (a : NovikovModule R F) :
    actionFieldMap hF ρ r a =
      map ρ (Sigma.map id fun i p => E.coprod (AddMonoidHom.id ℝ) (p -ᵥ r i))
        (actionFieldPotential_energy hF r) a :=
  (rfl)

variable [Finite ι]

/-- **The action-field specialization in coordinates.** In the lift coordinates of `r` and of the
energy `0` in each orbit, the action-field specialization of completed combinations is the
action-field map `TauCeti.NovikovSeries.actionFieldMap E ρ` of Novikov series in each orbit. -/
theorem coordinates_actionFieldMap (r : ∀ i, P i) (a : NovikovModule R F) (i : ι) :
    coordinates (actionFieldPotential_vadd F r) (fun _ => 0) (actionFieldMap hF ρ r a) i =
      NovikovSeries.actionFieldMap E ρ (coordinates hF r a i) := by
  have h := coordinates_map hF (actionFieldPotential_vadd F r) ρ
    (NovikovSeries.exists_period_rescale_coprod_id E) (vadd_vsub_energy r)
    (actionFieldPotential_energy hF r) r a i
  simp only [vsub_self, map_zero] at h
  rw [actionFieldMap_apply, h, NovikovSeries.actionFieldMap_eq_mapRingHom]

/-- The action-field specialization is semilinear for the Novikov module structures of
`TauCeti.NovikovModule.module`, over the action-field map of Novikov rings. -/
theorem actionFieldMap_smul (r : ∀ i, P i)
    (β : NovikovSeries R (G × ℝ) (E.coprod (AddMonoidHom.id ℝ))) (a : NovikovModule R F) :
    letI := module (R := R) hF
    letI := module (R := k) (actionFieldPotential_vadd F r)
    actionFieldMap hF ρ r (β • a) =
      NovikovSeries.actionFieldMap E ρ β • actionFieldMap hF ρ r a := by
  rw [actionFieldMap_apply, actionFieldMap_apply, NovikovSeries.actionFieldMap_eq_mapRingHom]
  exact map_smul_novikov hF (actionFieldPotential_vadd F r) ρ
    (NovikovSeries.exists_period_rescale_coprod_id E) (vadd_vsub_energy r) _ β a

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring k] (ρ : R →+* k) [Finite ι] [Finite ι₀]

/-- **Specializing the map of a matrix.** The action-field specialization carries the
Novikov-linear map of a matrix `M` of action-weighted Novikov series to the map of the matrix of
the action-field images `TauCeti.NovikovSeries.actionFieldMap E ρ` of its entries, relative to the
energy `0` in each orbit. -/
theorem actionFieldMap_novikovMapOfMatrix (r : ∀ i, P i) (r₀ : ∀ k, P₀ k)
    (M : Matrix ι ι₀ (NovikovSeries R (G × ℝ) (E.coprod (AddMonoidHom.id ℝ))))
    (a : NovikovModule R F) :
    actionFieldMap hF₀ ρ r₀ (novikovMapOfMatrix hF hF₀ r r₀ M a) =
      novikovMapOfMatrix (actionFieldPotential_vadd F r) (actionFieldPotential_vadd F₀ r₀)
        (fun _ => 0) (fun _ => 0) (M.map (NovikovSeries.actionFieldMap E ρ))
        (actionFieldMap hF ρ r a) := by
  have := Fintype.ofFinite ι
  refine (coordinates (actionFieldPotential_vadd F₀ r₀) fun _ => 0).injective
    (funext fun k => ?_)
  rw [coordinates_actionFieldMap, coordinates_novikovMapOfMatrix,
    coordinates_novikovMapOfMatrix, map_sum]
  simp only [map_mul, Matrix.map_apply, coordinates_actionFieldMap]

end CommSemiring

end ActionField

end NovikovModule

end TauCeti
