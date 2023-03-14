# Changelog (unreleased)

## [Unreleased]

### Added

- in `contructive_ereal.v`:
  + lemmas `ereal_blatticeMixin`, `ereal_tblatticeMixin`
  + canonicals `ereal_blatticeType`, `ereal_tblatticeType`
- in `lebesgue_measure.v`:
  + lemma `emeasurable_itv`
- in `exp.v`:
  + new lemmas `power_pos_ge0`, `power_pos0`, `power12_sqrt`

### Changed

- in `exp.v`:
  + generalize `exp_fun` and rename to `power_pos`
  + `exp_fun_gt0` has now a condition and is renamed to `power_pos_gt0`
  + weaken condition of `exp_funr1` and rename to `power_posr1`
  + weaken condition of `exp_fun_inv` and rename to `power_pos_inv`
  + `exp_funr0` -> `power_posr0`
  + `exp_fun1` -> `power_pos1`
  + `ler_exp_fun` -> `ler_power_pos`
  + `exp_funD` -> `power_posD`
  + `exp_fun_mulrn` -> `power_pos_mulrn`
  + the notation ``` `^ ``` has now scope `real_scope`
  + weaken condition of `riemannR_gt0` and `dvg_riemannR`

### Renamed

- in `lebesgue_measure.v`:
  + `punct_eitv_bnd_pinfty` -> `punct_eitv_bndy`
  + `punct_eitv_ninfty_bnd` -> `punct_eitv_Nybnd`
  + `eset1_pinfty` -> `eset1y`
  + `eset1_ninfty` -> `eset1Ny`
  + `ErealGenOInfty.measurable_set1_ninfty` -> `ErealGenOInfty.measurable_set1Ny`
  + `ErealGenOInfty.measurable_set1_pinfty` -> `ErealGenOInfty.measurable_set1y`
  + `ErealGenCInfty.measurable_set1_ninfty` -> `ErealGenCInfty.measurable_set1Ny`
  + `ErealGenCInfty.measurable_set1_pinfty` -> `ErealGenCInfty.measurable_set1y`

### Generalized

### Deprecated

- in `lebesgue_measure.v`:
  + lemmas `emeasurable_itv_bnd_pinfty`, `emeasurable_itv_ninfty_bnd`
    (use `emeasurable_itv` instead)

### Removed

### Infrastructure

### Misc
